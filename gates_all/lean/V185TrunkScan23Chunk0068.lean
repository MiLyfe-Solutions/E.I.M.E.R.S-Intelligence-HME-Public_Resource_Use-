import V185TrunkScan23Chunk0067

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_402953 : List Nat := [1, 2, 1, 1, 3, 1, 6, 1, 2, 3, 2]
def baseStart_402953 : Nat := 118140960795 + 402953 * 2 ^ 59
def prefixEnd_402953 : Nat := 4983230072969 + 3 ^ 40 * 402953 * 2
def baseEnd_402953 : Nat := 206908570171267178234359

theorem tailTrace_402953 : CollatzResearch.WordTrace tailWord_402953 prefixEnd_402953 206908570171267178234359 := by
  unfold tailWord_402953
  simp only [CollatzResearch.WordTrace]
  refine ⟨14696903309177574738557513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9797935539451716492371675 14696903309177574738557513)
  ·
    refine ⟨11022677481883181053918135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14696903309177574738557513 11022677481883181053918135)
    ·
      refine ⟨16534016222824771580877203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11022677481883181053918135 16534016222824771580877203)
      ·
        refine ⟨24801024334237157371315805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16534016222824771580877203 24801024334237157371315805)
        ·
          refine ⟨9300384125338934014243427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24801024334237157371315805 9300384125338934014243427)
          ·
            refine ⟨13950576188008401021365141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9300384125338934014243427 13950576188008401021365141)
            ·
              refine ⟨653933258812893797876491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13950576188008401021365141 653933258812893797876491)
              ·
                refine ⟨980899888219340696814737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653933258812893797876491 980899888219340696814737)
                ·
                  refine ⟨735674916164505522611053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980899888219340696814737 735674916164505522611053)
                  ·
                    refine ⟨275878093561689570979145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 735674916164505522611053 275878093561689570979145)
                    ·
                      refine ⟨206908570171267178234359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275878093561689570979145 206908570171267178234359)
                      ·
                        rfl

theorem cell23_402953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 3, 2].length) (baseStart_402953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402953 prefixEnd_402953 := by exact prefixLift 402953
  have htrace : WordTrace (prefixWord ++ tailWord_402953) baseStart_402953 baseEnd_402953 := by
    simpa [prefixWord, tailWord_402953, baseEnd_402953] using wordTrace_append hprefix tailTrace_402953
  have hstable : (prefixWord ++ tailWord_402953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402953).length < 2 ^ (prefixWord ++ tailWord_402953).sum := by decide
  have hdescent : baseEnd_402953 < baseStart_402953 := by decide
  rcases family_descends (prefixWord ++ tailWord_402953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402963 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 1, 5]
def baseStart_402963 : Nat := 118140960795 + 402963 * 2 ^ 59
def prefixEnd_402963 : Nat := 4983230072969 + 3 ^ 40 * 402963 * 2
def baseEnd_402963 : Nat := 68971234992604046369771

theorem tailTrace_402963 : CollatzResearch.WordTrace tailWord_402963 prefixEnd_402963 68971234992604046369771 := by
  unfold tailWord_402963
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697268039141346446421543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9798178692760897630947695 14697268039141346446421543)
  ·
    refine ⟨22045902058712019669632315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14697268039141346446421543 22045902058712019669632315)
    ·
      refine ⟨33068853088068029504448473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22045902058712019669632315 33068853088068029504448473)
      ·
        refine ⟨24801639816051022128336355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33068853088068029504448473 24801639816051022128336355)
        ·
          refine ⟨37202459724076533192504533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24801639816051022128336355 37202459724076533192504533)
          ·
            refine ⟨871932649783043746699325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 37202459724076533192504533 871932649783043746699325)
            ·
              refine ⟨326974743668641405012247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871932649783043746699325 326974743668641405012247)
              ·
                refine ⟨490462115502962107518371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326974743668641405012247 490462115502962107518371)
                ·
                  refine ⟨735693173254443161277557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490462115502962107518371 735693173254443161277557)
                  ·
                    refine ⟨68971234992604046369771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 735693173254443161277557 68971234992604046369771)
                    ·
                      rfl

theorem cell23_402963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 1, 5].length) (baseStart_402963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402963 prefixEnd_402963 := by exact prefixLift 402963
  have htrace : WordTrace (prefixWord ++ tailWord_402963) baseStart_402963 baseEnd_402963 := by
    simpa [prefixWord, tailWord_402963, baseEnd_402963] using wordTrace_append hprefix tailTrace_402963
  have hstable : (prefixWord ++ tailWord_402963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402963).length < 2 ^ (prefixWord ++ tailWord_402963).sum := by decide
  have hdescent : baseEnd_402963 < baseStart_402963 := by decide
  rcases family_descends (prefixWord ++ tailWord_402963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402977 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 1, 1, 3]
def baseStart_402977 : Nat := 118140960795 + 402977 * 2 ^ 59
def prefixEnd_402977 : Nat := 4983230072969 + 3 ^ 40 * 402977 * 2
def baseEnd_402977 : Nat := 206920893706975084334249

theorem tailTrace_402977 : CollatzResearch.WordTrace tailWord_402977 prefixEnd_402977 206920893706975084334249 := by
  unfold tailWord_402977
  simp only [CollatzResearch.WordTrace]
  refine ⟨14697778661090626837431185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9798519107393751224954123 14697778661090626837431185)
  ·
    refine ⟨11023333995817970128073389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14697778661090626837431185 11023333995817970128073389)
    ·
      refine ⟨4133750248431738798027521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11023333995817970128073389 4133750248431738798027521)
      ·
        refine ⟨3100312686323804098520641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4133750248431738798027521 3100312686323804098520641)
        ·
          refine ⟨2325234514742853073890481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3100312686323804098520641 2325234514742853073890481)
          ·
            refine ⟨1743925886057139805417861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2325234514742853073890481 1743925886057139805417861)
            ·
              refine ⟨326986103635713713515849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1743925886057139805417861 326986103635713713515849)
              ·
                refine ⟨245239577726785285136887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 326986103635713713515849 245239577726785285136887)
                ·
                  refine ⟨367859366590177927705331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245239577726785285136887 367859366590177927705331)
                  ·
                    refine ⟨551789049885266891557997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367859366590177927705331 551789049885266891557997)
                    ·
                      refine ⟨206920893706975084334249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551789049885266891557997 206920893706975084334249)
                      ·
                        rfl

theorem cell23_402977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 1, 1, 3].length) (baseStart_402977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402977 prefixEnd_402977 := by exact prefixLift 402977
  have htrace : WordTrace (prefixWord ++ tailWord_402977) baseStart_402977 baseEnd_402977 := by
    simpa [prefixWord, tailWord_402977, baseEnd_402977] using wordTrace_append hprefix tailTrace_402977
  have hstable : (prefixWord ++ tailWord_402977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402977).length < 2 ^ (prefixWord ++ tailWord_402977).sum := by decide
  have hdescent : baseEnd_402977 < baseStart_402977 := by decide
  rcases family_descends (prefixWord ++ tailWord_402977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402986 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_402986 : Nat := 118140960795 + 402986 * 2 ^ 59
def prefixEnd_402986 : Nat := 4983230072969 + 3 ^ 40 * 402986 * 2
def baseEnd_402986 : Nat := 206925515032865549121707

theorem tailTrace_402986 : CollatzResearch.WordTrace tailWord_402986 prefixEnd_402986 206925515032865549121707 := by
  unfold tailWord_402986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674526729514505343627203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9798737945372014249672541 3674526729514505343627203)
  ·
    refine ⟨5511790094271758015440805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674526729514505343627203 5511790094271758015440805)
    ·
      refine ⟨1033460642675954627895151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5511790094271758015440805 1033460642675954627895151)
      ·
        refine ⟨1550190964013931941842727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033460642675954627895151 1550190964013931941842727)
        ·
          refine ⟨2325286446020897912764091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550190964013931941842727 2325286446020897912764091)
          ·
            refine ⟨3487929669031346869146137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2325286446020897912764091 3487929669031346869146137)
            ·
              refine ⟨2615947251773510151859603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3487929669031346869146137 2615947251773510151859603)
              ·
                refine ⟨3923920877660265227789405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2615947251773510151859603 3923920877660265227789405)
                ·
                  refine ⟨1471470329122599460421027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3923920877660265227789405 1471470329122599460421027)
                  ·
                    refine ⟨2207205493683899190631541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1471470329122599460421027 2207205493683899190631541)
                    ·
                      refine ⟨206925515032865549121707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2207205493683899190631541 206925515032865549121707)
                      ·
                        rfl

theorem cell23_402986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_402986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_402986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_402986 prefixEnd_402986 := by exact prefixLift 402986
  have htrace : WordTrace (prefixWord ++ tailWord_402986) baseStart_402986 baseEnd_402986 := by
    simpa [prefixWord, tailWord_402986, baseEnd_402986] using wordTrace_append hprefix tailTrace_402986
  have hstable : (prefixWord ++ tailWord_402986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402986).length < 2 ^ (prefixWord ++ tailWord_402986).sum := by decide
  have hdescent : baseEnd_402986 < baseStart_402986 := by decide
  rcases family_descends (prefixWord ++ tailWord_402986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403000 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2]
def baseStart_403000 : Nat := 118140960795 + 403000 * 2 ^ 59
def prefixEnd_403000 : Nat := 4983230072969 + 3 ^ 40 * 403000 * 2
def baseEnd_403000 : Nat := 206932703762028494346643

theorem tailTrace_403000 : CollatzResearch.WordTrace tailWord_403000 prefixEnd_403000 206932703762028494346643 := by
  unfold tailWord_403000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349308770003650882759227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9799078360004867843678969 7349308770003650882759227)
  ·
    refine ⟨11023963155005476324138841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7349308770003650882759227 11023963155005476324138841)
    ·
      refine ⟨8267972366254107243104131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11023963155005476324138841 8267972366254107243104131)
      ·
        refine ⟨12401958549381160864656197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267972366254107243104131 12401958549381160864656197)
        ·
          refine ⟨2325367228008967662123037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12401958549381160864656197 2325367228008967662123037)
          ·
            refine ⟨872012710503362873296139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2325367228008967662123037 872012710503362873296139)
            ·
              refine ⟨1308019065755044309944209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872012710503362873296139 1308019065755044309944209)
              ·
                refine ⟨981014299316283232458157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1308019065755044309944209 981014299316283232458157)
                ·
                  refine ⟨367880362243606212171809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981014299316283232458157 367880362243606212171809)
                  ·
                    refine ⟨275910271682704659128857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 367880362243606212171809 275910271682704659128857)
                    ·
                      refine ⟨206932703762028494346643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 275910271682704659128857 206932703762028494346643)
                      ·
                        rfl

theorem cell23_403000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_403000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403000 prefixEnd_403000 := by exact prefixLift 403000
  have htrace : WordTrace (prefixWord ++ tailWord_403000) baseStart_403000 baseEnd_403000 := by
    simpa [prefixWord, tailWord_403000, baseEnd_403000] using wordTrace_append hprefix tailTrace_403000
  have hstable : (prefixWord ++ tailWord_403000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403000).length < 2 ^ (prefixWord ++ tailWord_403000).sum := by decide
  have hdescent : baseEnd_403000 < baseStart_403000 := by decide
  rcases family_descends (prefixWord ++ tailWord_403000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403014 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_403014 : Nat := 118140960795 + 403014 * 2 ^ 59
def prefixEnd_403014 : Nat := 4983230072969 + 3 ^ 40 * 403014 * 2
def baseEnd_403014 : Nat := 68979964163730479857193

theorem tailTrace_403014 : CollatzResearch.WordTrace tailWord_403014 prefixEnd_403014 68979964163730479857193 := by
  unfold tailWord_403014
  simp only [CollatzResearch.WordTrace]
  refine ⟨459347755061143192391503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9799418774637721437685397 459347755061143192391503)
  ·
    refine ⟨689021632591714788587255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 459347755061143192391503 689021632591714788587255)
    ·
      refine ⟨1033532448887572182880883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689021632591714788587255 1033532448887572182880883)
      ·
        refine ⟨1550298673331358274321325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033532448887572182880883 1550298673331358274321325)
        ·
          refine ⟨581362002499259352870497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1550298673331358274321325 581362002499259352870497)
          ·
            refine ⟨436021501874444514652873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581362002499259352870497 436021501874444514652873)
            ·
              refine ⟨327016126405833385989655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436021501874444514652873 327016126405833385989655)
              ·
                refine ⟨490524189608750078984483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327016126405833385989655 490524189608750078984483)
                ·
                  refine ⟨735786284413125118476725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490524189608750078984483 735786284413125118476725)
                  ·
                    refine ⟨68979964163730479857193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 735786284413125118476725 68979964163730479857193)
                    ·
                      rfl

theorem cell23_403014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_403014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403014 prefixEnd_403014 := by exact prefixLift 403014
  have htrace : WordTrace (prefixWord ++ tailWord_403014) baseStart_403014 baseEnd_403014 := by
    simpa [prefixWord, tailWord_403014, baseEnd_403014] using wordTrace_append hprefix tailTrace_403014
  have hstable : (prefixWord ++ tailWord_403014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403014).length < 2 ^ (prefixWord ++ tailWord_403014).sum := by decide
  have hdescent : baseEnd_403014 < baseStart_403014 := by decide
  rcases family_descends (prefixWord ++ tailWord_403014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403020 : List Nat := [2, 2, 1, 3, 1, 3, 4, 1, 1, 2, 3]
def baseStart_403020 : Nat := 118140960795 + 403020 * 2 ^ 59
def prefixEnd_403020 : Nat := 4983230072969 + 3 ^ 40 * 403020 * 2
def baseEnd_403020 : Nat := 206942973375118416096551

theorem tailTrace_403020 : CollatzResearch.WordTrace tailWord_403020 prefixEnd_403020 206942973375118416096551 := by
  unfold tailWord_403020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349673499967422590623257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9799564666623230120831009 7349673499967422590623257)
  ·
    refine ⟨5512255124975566942967443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7349673499967422590623257 5512255124975566942967443)
    ·
      refine ⟨8268382687463350414451165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5512255124975566942967443 8268382687463350414451165)
      ·
        refine ⟨3100643507798756405419187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8268382687463350414451165 3100643507798756405419187)
        ·
          refine ⟨4650965261698134608128781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100643507798756405419187 4650965261698134608128781)
          ·
            refine ⟨1744111973136800478048293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4650965261698134608128781 1744111973136800478048293)
            ·
              refine ⟨327020994963150089634055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1744111973136800478048293 327020994963150089634055)
              ·
                refine ⟨490531492444725134451083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327020994963150089634055 490531492444725134451083)
                ·
                  refine ⟨735797238667087701676625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490531492444725134451083 735797238667087701676625)
                  ·
                    refine ⟨551847929000315776257469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 735797238667087701676625 551847929000315776257469)
                    ·
                      refine ⟨206942973375118416096551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551847929000315776257469 206942973375118416096551)
                      ·
                        rfl

theorem cell23_403020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_403020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403020 prefixEnd_403020 := by exact prefixLift 403020
  have htrace : WordTrace (prefixWord ++ tailWord_403020) baseStart_403020 baseEnd_403020 := by
    simpa [prefixWord, tailWord_403020, baseEnd_403020] using wordTrace_append hprefix tailTrace_403020
  have hstable : (prefixWord ++ tailWord_403020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403020).length < 2 ^ (prefixWord ++ tailWord_403020).sum := by decide
  have hdescent : baseEnd_403020 < baseStart_403020 := by decide
  rcases family_descends (prefixWord ++ tailWord_403020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403050 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3]
def baseStart_403050 : Nat := 118140960795 + 403050 * 2 ^ 59
def prefixEnd_403050 : Nat := 4983230072969 + 3 ^ 40 * 403050 * 2
def baseEnd_403050 : Nat := 206958377794753298721413

theorem tailTrace_403050 : CollatzResearch.WordTrace tailWord_403050 prefixEnd_403050 206958377794753298721413 := by
  unfold tailWord_403050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3675110297456540076209651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9800294126550773536559069 3675110297456540076209651)
  ·
    refine ⟨5512665446184810114314477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3675110297456540076209651 5512665446184810114314477)
    ·
      refine ⟨2067249542319303792867929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5512665446184810114314477 2067249542319303792867929)
      ·
        refine ⟨1550437156739477844650947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067249542319303792867929 1550437156739477844650947)
        ·
          refine ⟨2325655735109216766976421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1550437156739477844650947 2325655735109216766976421)
          ·
            refine ⟨436060450332978143808079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2325655735109216766976421 436060450332978143808079)
            ·
              refine ⟨654090675499467215712119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436060450332978143808079 654090675499467215712119)
              ·
                refine ⟨981136013249200823568179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654090675499467215712119 981136013249200823568179)
                ·
                  refine ⟨1471704019873801235352269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981136013249200823568179 1471704019873801235352269)
                  ·
                    refine ⟨551889007452675463257101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1471704019873801235352269 551889007452675463257101)
                    ·
                      refine ⟨206958377794753298721413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 551889007452675463257101 206958377794753298721413)
                      ·
                        rfl

theorem cell23_403050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_403050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403050 prefixEnd_403050 := by exact prefixLift 403050
  have htrace : WordTrace (prefixWord ++ tailWord_403050) baseStart_403050 baseEnd_403050 := by
    simpa [prefixWord, tailWord_403050, baseEnd_403050] using wordTrace_append hprefix tailTrace_403050
  have hstable : (prefixWord ++ tailWord_403050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403050).length < 2 ^ (prefixWord ++ tailWord_403050).sum := by decide
  have hdescent : baseEnd_403050 < baseStart_403050 := by decide
  rcases family_descends (prefixWord ++ tailWord_403050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403136 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5]
def baseStart_403136 : Nat := 118140960795 + 403136 * 2 ^ 59
def prefixEnd_403136 : Nat := 4983230072969 + 3 ^ 40 * 403136 * 2
def baseEnd_403136 : Nat := 207002537131039962246017

theorem tailTrace_403136 : CollatzResearch.WordTrace tailWord_403136 prefixEnd_403136 207002537131039962246017 := by
  unfold tailWord_403136
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351788933757298496234631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9802385245009731328312841 7351788933757298496234631)
  ·
    refine ⟨11027683400635947744351947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7351788933757298496234631 11027683400635947744351947)
    ·
      refine ⟨16541525100953921616527921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11027683400635947744351947 16541525100953921616527921)
      ·
        refine ⟨12406143825715441212395941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16541525100953921616527921 12406143825715441212395941)
        ·
          refine ⟨2326151967321645227324239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12406143825715441212395941 2326151967321645227324239)
          ·
            refine ⟨3489227950982467840986359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326151967321645227324239 3489227950982467840986359)
            ·
              refine ⟨5233841926473701761479539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489227950982467840986359 5233841926473701761479539)
              ·
                refine ⟨7850762889710552642219309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5233841926473701761479539 7850762889710552642219309)
                ·
                  refine ⟨2944036083641457240832241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7850762889710552642219309 2944036083641457240832241)
                  ·
                    refine ⟨2208027062731092930624181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2944036083641457240832241 2208027062731092930624181)
                    ·
                      refine ⟨207002537131039962246017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2208027062731092930624181 207002537131039962246017)
                      ·
                        rfl

theorem cell23_403136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_403136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403136 prefixEnd_403136 := by exact prefixLift 403136
  have htrace : WordTrace (prefixWord ++ tailWord_403136) baseStart_403136 baseEnd_403136 := by
    simpa [prefixWord, tailWord_403136, baseEnd_403136] using wordTrace_append hprefix tailTrace_403136
  have hstable : (prefixWord ++ tailWord_403136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403136).length < 2 ^ (prefixWord ++ tailWord_403136).sum := by decide
  have hdescent : baseEnd_403136 < baseStart_403136 := by decide
  rcases family_descends (prefixWord ++ tailWord_403136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403183 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_403183 : Nat := 118140960795 + 403183 * 2 ^ 59
def prefixEnd_403183 : Nat := 4983230072969 + 3 ^ 40 * 403183 * 2
def baseEnd_403183 : Nat := 207026670721801278358301

theorem tailTrace_403183 : CollatzResearch.WordTrace tailWord_403183 prefixEnd_403183 207026670721801278358301 := by
  unfold tailWord_403183
  simp only [CollatzResearch.WordTrace]
  refine ⟨14705292098344324019430203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9803528065562882679620135 14705292098344324019430203)
  ·
    refine ⟨22057938147516486029145305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14705292098344324019430203 22057938147516486029145305)
    ·
      refine ⟨16543453610637364521858979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22057938147516486029145305 16543453610637364521858979)
      ·
        refine ⟨24815180415956046782788469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16543453610637364521858979 24815180415956046782788469)
        ·
          refine ⟨2326423163995879385886419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24815180415956046782788469 2326423163995879385886419)
          ·
            refine ⟨3489634745993819078829629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2326423163995879385886419 3489634745993819078829629)
            ·
              refine ⟨1308613029747682154561111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3489634745993819078829629 1308613029747682154561111)
              ·
                refine ⟨1962919544621523231841667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308613029747682154561111 1962919544621523231841667)
                ·
                  refine ⟨2944379316932284847762501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962919544621523231841667 2944379316932284847762501)
                  ·
                    refine ⟨552071121924803408955469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2944379316932284847762501 552071121924803408955469)
                    ·
                      refine ⟨207026670721801278358301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552071121924803408955469 207026670721801278358301)
                      ·
                        rfl

theorem cell23_403183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_403183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403183 prefixEnd_403183 := by exact prefixLift 403183
  have htrace : WordTrace (prefixWord ++ tailWord_403183) baseStart_403183 baseEnd_403183 := by
    simpa [prefixWord, tailWord_403183, baseEnd_403183] using wordTrace_append hprefix tailTrace_403183
  have hstable : (prefixWord ++ tailWord_403183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403183).length < 2 ^ (prefixWord ++ tailWord_403183).sum := by decide
  have hdescent : baseEnd_403183 < baseStart_403183 := by decide
  rcases family_descends (prefixWord ++ tailWord_403183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403203 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 6]
def baseStart_403203 : Nat := 118140960795 + 403203 * 2 ^ 59
def prefixEnd_403203 : Nat := 4983230072969 + 3 ^ 40 * 403203 * 2
def baseEnd_403203 : Nat := 23004104481654577789801

theorem tailTrace_403203 : CollatzResearch.WordTrace tailWord_403203 prefixEnd_403203 23004104481654577789801 := by
  unfold tailWord_403203
  simp only [CollatzResearch.WordTrace]
  refine ⟨14706021558271867435158263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9804014372181244956772175 14706021558271867435158263)
  ·
    refine ⟨22059032337407801152737395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14706021558271867435158263 22059032337407801152737395)
    ·
      refine ⟨33088548506111701729106093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22059032337407801152737395 33088548506111701729106093)
      ·
        refine ⟨12408205689791888148414785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33088548506111701729106093 12408205689791888148414785)
        ·
          refine ⟨9306154267343916111311089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12408205689791888148414785 9306154267343916111311089)
          ·
            refine ⟨6979615700507937083483317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9306154267343916111311089 6979615700507937083483317)
            ·
              refine ⟨654338971922619101576561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6979615700507937083483317 654338971922619101576561)
              ·
                refine ⟨490754228941964326182421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654338971922619101576561 490754228941964326182421)
                ·
                  refine ⟨23004104481654577789801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 490754228941964326182421 23004104481654577789801)
                  ·
                    rfl

theorem cell23_403203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 6].length) (baseStart_403203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403203 prefixEnd_403203 := by exact prefixLift 403203
  have htrace : WordTrace (prefixWord ++ tailWord_403203) baseStart_403203 baseEnd_403203 := by
    simpa [prefixWord, tailWord_403203, baseEnd_403203] using wordTrace_append hprefix tailTrace_403203
  have hstable : (prefixWord ++ tailWord_403203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403203).length < 2 ^ (prefixWord ++ tailWord_403203).sum := by decide
  have hdescent : baseEnd_403203 < baseStart_403203 := by decide
  rcases family_descends (prefixWord ++ tailWord_403203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403207 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 3, 4]
def baseStart_403207 : Nat := 118140960795 + 403207 * 2 ^ 59
def prefixEnd_403207 : Nat := 4983230072969 + 3 ^ 40 * 403207 * 2
def baseEnd_403207 : Nat := 69012998085836394819397

theorem tailTrace_403207 : CollatzResearch.WordTrace tailWord_403207 prefixEnd_403207 69012998085836394819397 := by
  unfold tailWord_403207
  simp only [CollatzResearch.WordTrace]
  refine ⟨14706167450257376118303875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9804111633504917412202583 14706167450257376118303875)
  ·
    refine ⟨22059251175386064177455813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14706167450257376118303875 22059251175386064177455813)
    ·
      refine ⟨4136109595384887033272965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22059251175386064177455813 4136109595384887033272965)
      ·
        refine ⟨775520549134666318738681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4136109595384887033272965 775520549134666318738681)
        ·
          refine ⟨581640411850999739054011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775520549134666318738681 581640411850999739054011)
          ·
            refine ⟨872460617776499608581017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581640411850999739054011 872460617776499608581017)
            ·
              refine ⟨654345463332374706435763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872460617776499608581017 654345463332374706435763)
              ·
                refine ⟨981518194998562059653645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654345463332374706435763 981518194998562059653645)
                ·
                  refine ⟨368069323124460772370117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981518194998562059653645 368069323124460772370117)
                  ·
                    refine ⟨69012998085836394819397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368069323124460772370117 69012998085836394819397)
                    ·
                      rfl

theorem cell23_403207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_403207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403207 prefixEnd_403207 := by exact prefixLift 403207
  have htrace : WordTrace (prefixWord ++ tailWord_403207) baseStart_403207 baseEnd_403207 := by
    simpa [prefixWord, tailWord_403207, baseEnd_403207] using wordTrace_append hprefix tailTrace_403207
  have hstable : (prefixWord ++ tailWord_403207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403207).length < 2 ^ (prefixWord ++ tailWord_403207).sum := by decide
  have hdescent : baseEnd_403207 < baseStart_403207 := by decide
  rcases family_descends (prefixWord ++ tailWord_403207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403250 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 1, 5]
def baseStart_403250 : Nat := 118140960795 + 403250 * 2 ^ 59
def prefixEnd_403250 : Nat := 4983230072969 + 3 ^ 40 * 403250 * 2
def baseEnd_403250 : Nat := 69020357975217505406831

theorem tailTrace_403250 : CollatzResearch.WordTrace tailWord_403250 prefixEnd_403250 69020357975217505406831 := by
  unfold tailWord_403250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676933947275398615529801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9805157192734396308079469 3676933947275398615529801)
  ·
    refine ⟨2757700460456548961647351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3676933947275398615529801 2757700460456548961647351)
    ·
      refine ⟨4136550690684823442471027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2757700460456548961647351 4136550690684823442471027)
      ·
        refine ⟨6204826036027235163706541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4136550690684823442471027 6204826036027235163706541)
        ·
          refine ⟨2326809763510213186389953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6204826036027235163706541 2326809763510213186389953)
          ·
            refine ⟨1745107322632659889792465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2326809763510213186389953 1745107322632659889792465)
            ·
              refine ⟨1308830491974494917344349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745107322632659889792465 1308830491974494917344349)
              ·
                refine ⟨490811434490435594004131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1308830491974494917344349 490811434490435594004131)
                ·
                  refine ⟨736217151735653391006197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490811434490435594004131 736217151735653391006197)
                  ·
                    refine ⟨69020357975217505406831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 736217151735653391006197 69020357975217505406831)
                    ·
                      rfl

theorem cell23_403250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_403250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403250 prefixEnd_403250 := by exact prefixLift 403250
  have htrace : WordTrace (prefixWord ++ tailWord_403250) baseStart_403250 baseEnd_403250 := by
    simpa [prefixWord, tailWord_403250, baseEnd_403250] using wordTrace_append hprefix tailTrace_403250
  have hstable : (prefixWord ++ tailWord_403250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403250).length < 2 ^ (prefixWord ++ tailWord_403250).sum := by decide
  have hdescent : baseEnd_403250 < baseStart_403250 := by decide
  rcases family_descends (prefixWord ++ tailWord_403250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403273 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 5]
def baseStart_403273 : Nat := 118140960795 + 403273 * 2 ^ 59
def prefixEnd_403273 : Nat := 4983230072969 + 3 ^ 40 * 403273 * 2
def baseEnd_403273 : Nat := 207072883980705926232887

theorem tailTrace_403273 : CollatzResearch.WordTrace tailWord_403273 prefixEnd_403273 207072883980705926232887 := by
  unfold tailWord_403273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14708574668018269390206473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9805716445345512926804315 14708574668018269390206473)
  ·
    refine ⟨11031431001013702042654855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14708574668018269390206473 11031431001013702042654855)
    ·
      refine ⟨16547146501520553063982283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11031431001013702042654855 16547146501520553063982283)
      ·
        refine ⟨24820719752280829595973425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16547146501520553063982283 24820719752280829595973425)
        ·
          refine ⟨18615539814210622196980069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24820719752280829595973425 18615539814210622196980069)
          ·
            refine ⟨3490413715164491661933763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18615539814210622196980069 3490413715164491661933763)
            ·
              refine ⟨5235620572746737492900645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490413715164491661933763 5235620572746737492900645)
              ·
                refine ⟨981678857390013279918871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5235620572746737492900645 981678857390013279918871)
                ·
                  refine ⟨1472518286085019919878307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 981678857390013279918871 1472518286085019919878307)
                  ·
                    refine ⟨2208777429127529879817461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1472518286085019919878307 2208777429127529879817461)
                    ·
                      refine ⟨207072883980705926232887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2208777429127529879817461 207072883980705926232887)
                      ·
                        rfl

theorem cell23_403273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 1, 5].length) (baseStart_403273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403273 prefixEnd_403273 := by exact prefixLift 403273
  have htrace : WordTrace (prefixWord ++ tailWord_403273) baseStart_403273 baseEnd_403273 := by
    simpa [prefixWord, tailWord_403273, baseEnd_403273] using wordTrace_append hprefix tailTrace_403273
  have hstable : (prefixWord ++ tailWord_403273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403273).length < 2 ^ (prefixWord ++ tailWord_403273).sum := by decide
  have hdescent : baseEnd_403273 < baseStart_403273 := by decide
  rcases family_descends (prefixWord ++ tailWord_403273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403290 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_403290 : Nat := 118140960795 + 403290 * 2 ^ 59
def prefixEnd_403290 : Nat := 4983230072969 + 3 ^ 40 * 403290 * 2
def baseEnd_403290 : Nat := 207081613151832359720309

theorem tailTrace_403290 : CollatzResearch.WordTrace tailWord_403290 prefixEnd_403290 207081613151832359720309 := by
  unfold tailWord_403290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3677298677239170323393831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9806129805971120862383549 3677298677239170323393831)
  ·
    refine ⟨5515948015858755485090747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3677298677239170323393831 5515948015858755485090747)
    ·
      refine ⟨8273922023788133227636121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5515948015858755485090747 8273922023788133227636121)
      ·
        refine ⟨6205441517841099920727091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8273922023788133227636121 6205441517841099920727091)
        ·
          refine ⟨9308162276761649881090637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6205441517841099920727091 9308162276761649881090637)
          ·
            refine ⟨3490560853785618705408989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9308162276761649881090637 3490560853785618705408989)
            ·
              refine ⟨1308960320169607014528371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3490560853785618705408989 1308960320169607014528371)
              ·
                refine ⟨1963440480254410521792557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308960320169607014528371 1963440480254410521792557)
                ·
                  refine ⟨736290180095403945672209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1963440480254410521792557 736290180095403945672209)
                  ·
                    refine ⟨552217635071552959254157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736290180095403945672209 552217635071552959254157)
                    ·
                      refine ⟨207081613151832359720309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552217635071552959254157 207081613151832359720309)
                      ·
                        rfl

theorem cell23_403290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_403290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403290 prefixEnd_403290 := by exact prefixLift 403290
  have htrace : WordTrace (prefixWord ++ tailWord_403290) baseStart_403290 baseEnd_403290 := by
    simpa [prefixWord, tailWord_403290, baseEnd_403290] using wordTrace_append hprefix tailTrace_403290
  have hstable : (prefixWord ++ tailWord_403290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403290).length < 2 ^ (prefixWord ++ tailWord_403290).sum := by decide
  have hdescent : baseEnd_403290 < baseStart_403290 := by decide
  rcases family_descends (prefixWord ++ tailWord_403290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403320 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3]
def baseStart_403320 : Nat := 118140960795 + 403320 * 2 ^ 59
def prefixEnd_403320 : Nat := 4983230072969 + 3 ^ 40 * 403320 * 2
def baseEnd_403320 : Nat := 207097017571467242345171

theorem tailTrace_403320 : CollatzResearch.WordTrace tailWord_403320 prefixEnd_403320 207097017571467242345171 := by
  unfold tailWord_403320
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355144449423998208583707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9806859265898664278111609 7355144449423998208583707)
  ·
    refine ⟨11032716674135997312875561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7355144449423998208583707 11032716674135997312875561)
    ·
      refine ⟨8274537505601997984656671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11032716674135997312875561 8274537505601997984656671)
      ·
        refine ⟨12411806258402996976985007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8274537505601997984656671 12411806258402996976985007)
        ·
          refine ⟨18617709387604495465477511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12411806258402996976985007 18617709387604495465477511)
          ·
            refine ⟨27926564081406743198216267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18617709387604495465477511 27926564081406743198216267)
            ·
              refine ⟨41889846122110114797324401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27926564081406743198216267 41889846122110114797324401)
              ·
                refine ⟨31417384591582586097993301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41889846122110114797324401 31417384591582586097993301)
                ·
                  refine ⟨368172475682608430835859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31417384591582586097993301 368172475682608430835859)
                  ·
                    refine ⟨552258713523912646253789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 368172475682608430835859 552258713523912646253789)
                    ·
                      refine ⟨207097017571467242345171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552258713523912646253789 207097017571467242345171)
                      ·
                        rfl

theorem cell23_403320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_403320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403320 prefixEnd_403320 := by exact prefixLift 403320
  have htrace : WordTrace (prefixWord ++ tailWord_403320) baseStart_403320 baseEnd_403320 := by
    simpa [prefixWord, tailWord_403320, baseEnd_403320] using wordTrace_append hprefix tailTrace_403320
  have hstable : (prefixWord ++ tailWord_403320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403320).length < 2 ^ (prefixWord ++ tailWord_403320).sum := by decide
  have hdescent : baseEnd_403320 < baseStart_403320 := by decide
  rcases family_descends (prefixWord ++ tailWord_403320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403337 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 3]
def baseStart_403337 : Nat := 118140960795 + 403337 * 2 ^ 59
def prefixEnd_403337 : Nat := 4983230072969 + 3 ^ 40 * 403337 * 2
def baseEnd_403337 : Nat := 207105746742593675832593

theorem tailTrace_403337 : CollatzResearch.WordTrace tailWord_403337 prefixEnd_403337 207105746742593675832593 := by
  unfold tailWord_403337
  simp only [CollatzResearch.WordTrace]
  refine ⟨14710908939786408320536265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9807272626524272213690843 14710908939786408320536265)
  ·
    refine ⟨11033181704839806240402199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14710908939786408320536265 11033181704839806240402199)
    ·
      refine ⟨16549772557259709360603299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11033181704839806240402199 16549772557259709360603299)
      ·
        refine ⟨24824658835889564040904949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16549772557259709360603299 24824658835889564040904949)
        ·
          refine ⟨2327311765864646628834839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24824658835889564040904949 2327311765864646628834839)
          ·
            refine ⟨3490967648796969943252259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327311765864646628834839 3490967648796969943252259)
            ·
              refine ⟨5236451473195454914878389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3490967648796969943252259 5236451473195454914878389)
              ·
                refine ⟨490917325612073898269849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5236451473195454914878389 490917325612073898269849)
                ·
                  refine ⟨368187994209055423702387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490917325612073898269849 368187994209055423702387)
                  ·
                    refine ⟨552281991313583135553581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 368187994209055423702387 552281991313583135553581)
                    ·
                      refine ⟨207105746742593675832593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552281991313583135553581 207105746742593675832593)
                      ·
                        rfl

theorem cell23_403337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 1, 3].length) (baseStart_403337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403337 prefixEnd_403337 := by exact prefixLift 403337
  have htrace : WordTrace (prefixWord ++ tailWord_403337) baseStart_403337 baseEnd_403337 := by
    simpa [prefixWord, tailWord_403337, baseEnd_403337] using wordTrace_append hprefix tailTrace_403337
  have hstable : (prefixWord ++ tailWord_403337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403337).length < 2 ^ (prefixWord ++ tailWord_403337).sum := by decide
  have hdescent : baseEnd_403337 < baseStart_403337 := by decide
  rcases family_descends (prefixWord ++ tailWord_403337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403363 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_403363 : Nat := 118140960795 + 403363 * 2 ^ 59
def prefixEnd_403363 : Nat := 4983230072969 + 3 ^ 40 * 403363 * 2
def baseEnd_403363 : Nat := 207119097239610574107473

theorem tailTrace_403363 : CollatzResearch.WordTrace tailWord_403363 prefixEnd_403363 207119097239610574107473 := by
  unfold tailWord_403363
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711857237692214760982743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9807904825128143173988495 14711857237692214760982743)
  ·
    refine ⟨22067785856538322141474115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14711857237692214760982743 22067785856538322141474115)
    ·
      refine ⟨33101678784807483212211173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22067785856538322141474115 33101678784807483212211173)
      ·
        refine ⟨6206564772151403102289595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33101678784807483212211173 6206564772151403102289595)
        ·
          refine ⟨9309847158227104653434393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206564772151403102289595 9309847158227104653434393)
          ·
            refine ⟨6982385368670328490075795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9309847158227104653434393 6982385368670328490075795)
            ·
              refine ⟨10473578053005492735113693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6982385368670328490075795 10473578053005492735113693)
              ·
                refine ⟨3927591769877059775667635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10473578053005492735113693 3927591769877059775667635)
                ·
                  refine ⟨5891387654815589663501453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3927591769877059775667635 5891387654815589663501453)
                  ·
                    refine ⟨2209270370555846123813045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5891387654815589663501453 2209270370555846123813045)
                    ·
                      refine ⟨207119097239610574107473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2209270370555846123813045 207119097239610574107473)
                      ·
                        rfl

theorem cell23_403363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_403363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403363 prefixEnd_403363 := by exact prefixLift 403363
  have htrace : WordTrace (prefixWord ++ tailWord_403363) baseStart_403363 baseEnd_403363 := by
    simpa [prefixWord, tailWord_403363, baseEnd_403363] using wordTrace_append hprefix tailTrace_403363
  have hstable : (prefixWord ++ tailWord_403363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403363).length < 2 ^ (prefixWord ++ tailWord_403363).sum := by decide
  have hdescent : baseEnd_403363 < baseStart_403363 := by decide
  rcases family_descends (prefixWord ++ tailWord_403363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403364 : List Nat := [2, 3, 1, 2, 1, 4, 1, 3, 1, 3, 2]
def baseStart_403364 : Nat := 118140960795 + 403364 * 2 ^ 59
def prefixEnd_403364 : Nat := 4983230072969 + 3 ^ 40 * 403364 * 2
def baseEnd_403364 : Nat := 207119610720265070194969

theorem tailTrace_403364 : CollatzResearch.WordTrace tailWord_403364 prefixEnd_403364 207119610720265070194969 := by
  unfold tailWord_403364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7355946855344295965884573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9807929140459061287846097 7355946855344295965884573)
  ·
    refine ⟨2758480070754110987206715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7355946855344295965884573 2758480070754110987206715)
    ·
      refine ⟨4137720106131166480810073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2758480070754110987206715 4137720106131166480810073)
      ·
        refine ⟨3103290079598374860607555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4137720106131166480810073 3103290079598374860607555)
        ·
          refine ⟨4654935119397562290911333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3103290079598374860607555 4654935119397562290911333)
          ·
            refine ⟨872800334887042929545875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4654935119397562290911333 872800334887042929545875)
            ·
              refine ⟨1309200502330564394318813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872800334887042929545875 1309200502330564394318813)
              ·
                refine ⟨490950188373961647869555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1309200502330564394318813 490950188373961647869555)
                ·
                  refine ⟨736425282560942471804333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490950188373961647869555 736425282560942471804333)
                  ·
                    refine ⟨276159480960353426926625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 736425282560942471804333 276159480960353426926625)
                    ·
                      refine ⟨207119610720265070194969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276159480960353426926625 207119610720265070194969)
                      ·
                        rfl

theorem cell23_403364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_403364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403364 prefixEnd_403364 := by exact prefixLift 403364
  have htrace : WordTrace (prefixWord ++ tailWord_403364) baseStart_403364 baseEnd_403364 := by
    simpa [prefixWord, tailWord_403364, baseEnd_403364] using wordTrace_append hprefix tailTrace_403364
  have hstable : (prefixWord ++ tailWord_403364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403364).length < 2 ^ (prefixWord ++ tailWord_403364).sum := by decide
  have hdescent : baseEnd_403364 < baseStart_403364 := by decide
  rcases family_descends (prefixWord ++ tailWord_403364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403388 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 2, 1, 3]
def baseStart_403388 : Nat := 118140960795 + 403388 * 2 ^ 59
def prefixEnd_403388 : Nat := 4983230072969 + 3 ^ 40 * 403388 * 2
def baseEnd_403388 : Nat := 207131934255972976294859

theorem tailTrace_403388 : CollatzResearch.WordTrace tailWord_403388 prefixEnd_403388 207131934255972976294859 := by
  unfold tailWord_403388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356384531300822015321409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9808512708401096020428545 7356384531300822015321409)
  ·
    refine ⟨5517288398475616511491057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7356384531300822015321409 5517288398475616511491057)
    ·
      refine ⟨4137966298856712383618293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5517288398475616511491057 4137966298856712383618293)
      ·
        refine ⟨387934340517816785964215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4137966298856712383618293 387934340517816785964215)
        ·
          refine ⟨581901510776725178946323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387934340517816785964215 581901510776725178946323)
          ·
            refine ⟨872852266165087768419485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581901510776725178946323 872852266165087768419485)
            ·
              refine ⟨327319599811907913157307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872852266165087768419485 327319599811907913157307)
              ·
                refine ⟨490979399717861869735961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327319599811907913157307 490979399717861869735961)
                ·
                  refine ⟨368234549788396402301971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490979399717861869735961 368234549788396402301971)
                  ·
                    refine ⟨552351824682594603452957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 368234549788396402301971 552351824682594603452957)
                    ·
                      refine ⟨207131934255972976294859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552351824682594603452957 207131934255972976294859)
                      ·
                        rfl

theorem cell23_403388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_403388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403388 prefixEnd_403388 := by exact prefixLift 403388
  have htrace : WordTrace (prefixWord ++ tailWord_403388) baseStart_403388 baseEnd_403388 := by
    simpa [prefixWord, tailWord_403388, baseEnd_403388] using wordTrace_append hprefix tailTrace_403388
  have hstable : (prefixWord ++ tailWord_403388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403388).length < 2 ^ (prefixWord ++ tailWord_403388).sum := by decide
  have hdescent : baseEnd_403388 < baseStart_403388 := by decide
  rcases family_descends (prefixWord ++ tailWord_403388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403400 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 7]
def baseStart_403400 : Nat := 118140960795 + 403400 * 2 ^ 59
def prefixEnd_403400 : Nat := 4983230072969 + 3 ^ 40 * 403400 * 2
def baseEnd_403400 : Nat := 23015344002647436593867

theorem tailTrace_403400 : CollatzResearch.WordTrace tailWord_403400 prefixEnd_403400 23015344002647436593867 := by
  unfold tailWord_403400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356603369279085040039827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9808804492372113386719769 7356603369279085040039827)
  ·
    refine ⟨11034905053918627560059741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7356603369279085040039827 11034905053918627560059741)
    ·
      refine ⟨4138089395219485335022403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11034905053918627560059741 4138089395219485335022403)
      ·
        refine ⟨6207134092829228002533605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4138089395219485335022403 6207134092829228002533605)
        ·
          refine ⟨1163837642405480250475051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6207134092829228002533605 1163837642405480250475051)
          ·
            refine ⟨1745756463608220375712577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163837642405480250475051 1745756463608220375712577)
            ·
              refine ⟨1309317347706165281784433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1745756463608220375712577 1309317347706165281784433)
              ·
                refine ⟨981988010779623961338325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1309317347706165281784433 981988010779623961338325)
                ·
                  refine ⟨23015344002647436593867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 981988010779623961338325 23015344002647436593867)
                  ·
                    rfl

theorem cell23_403400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 7].length) (baseStart_403400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403400 prefixEnd_403400 := by exact prefixLift 403400
  have htrace : WordTrace (prefixWord ++ tailWord_403400) baseStart_403400 baseEnd_403400 := by
    simpa [prefixWord, tailWord_403400, baseEnd_403400] using wordTrace_append hprefix tailTrace_403400
  have hstable : (prefixWord ++ tailWord_403400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403400).length < 2 ^ (prefixWord ++ tailWord_403400).sum := by decide
  have hdescent : baseEnd_403400 < baseStart_403400 := by decide
  rcases family_descends (prefixWord ++ tailWord_403400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403414 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_403414 : Nat := 118140960795 + 403414 * 2 ^ 59
def prefixEnd_403414 : Nat := 4983230072969 + 3 ^ 40 * 403414 * 2
def baseEnd_403414 : Nat := 207145284752989874569739

theorem tailTrace_403414 : CollatzResearch.WordTrace tailWord_403414 prefixEnd_403414 207145284752989874569739 := by
  unfold tailWord_403414
  simp only [CollatzResearch.WordTrace]
  refine ⟨919607335031715654443081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9809144907004966980726197 919607335031715654443081)
  ·
    refine ⟨689705501273786740832311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 919607335031715654443081 689705501273786740832311)
    ·
      refine ⟨1034558251910680111248467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689705501273786740832311 1034558251910680111248467)
      ·
        refine ⟨1551837377866020166872701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034558251910680111248467 1551837377866020166872701)
        ·
          refine ⟨581939016699757562577263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1551837377866020166872701 581939016699757562577263)
          ·
            refine ⟨872908525049636343865895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581939016699757562577263 872908525049636343865895)
            ·
              refine ⟨1309362787574454515798843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872908525049636343865895 1309362787574454515798843)
              ·
                refine ⟨1964044181361681773698265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1309362787574454515798843 1964044181361681773698265)
                ·
                  refine ⟨1473033136021261330273699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1964044181361681773698265 1473033136021261330273699)
                  ·
                    refine ⟨2209549704031891995410549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1473033136021261330273699 2209549704031891995410549)
                    ·
                      refine ⟨207145284752989874569739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2209549704031891995410549 207145284752989874569739)
                      ·
                        rfl

theorem cell23_403414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_403414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403414 prefixEnd_403414 := by exact prefixLift 403414
  have htrace : WordTrace (prefixWord ++ tailWord_403414) baseStart_403414 baseEnd_403414 := by
    simpa [prefixWord, tailWord_403414, baseEnd_403414] using wordTrace_append hprefix tailTrace_403414
  have hstable : (prefixWord ++ tailWord_403414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403414).length < 2 ^ (prefixWord ++ tailWord_403414).sum := by decide
  have hdescent : baseEnd_403414 < baseStart_403414 := by decide
  rcases family_descends (prefixWord ++ tailWord_403414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403433 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 8]
def baseStart_403433 : Nat := 118140960795 + 403433 * 2 ^ 59
def prefixEnd_403433 : Nat := 4983230072969 + 3 ^ 40 * 403433 * 2
def baseEnd_403433 : Nat := 207155040885425300232151

theorem tailTrace_403433 : CollatzResearch.WordTrace tailWord_403433 prefixEnd_403433 207155040885425300232151 := by
  unfold tailWord_403433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14714410347438616716030953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9809606898292411144020635 14714410347438616716030953)
  ·
    refine ⟨11035807760578962537023215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14714410347438616716030953 11035807760578962537023215)
    ·
      refine ⟨16553711640868443805534823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11035807760578962537023215 16553711640868443805534823)
      ·
        refine ⟨24830567461302665708302235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16553711640868443805534823 24830567461302665708302235)
        ·
          refine ⟨37245851191953998562453353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24830567461302665708302235 37245851191953998562453353)
          ·
            refine ⟨27934388393965498921840015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37245851191953998562453353 27934388393965498921840015)
            ·
              refine ⟨41901582590948248382760023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27934388393965498921840015 41901582590948248382760023)
              ·
                refine ⟨62852373886422372574140035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41901582590948248382760023 62852373886422372574140035)
                ·
                  refine ⟨94278560829633558861210053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62852373886422372574140035 94278560829633558861210053)
                  ·
                    refine ⟨17677230155556292286476885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94278560829633558861210053 17677230155556292286476885)
                    ·
                      refine ⟨207155040885425300232151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17677230155556292286476885 207155040885425300232151)
                      ·
                        rfl

theorem cell23_403433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 4, 8].length) (baseStart_403433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403433 prefixEnd_403433 := by exact prefixLift 403433
  have htrace : WordTrace (prefixWord ++ tailWord_403433) baseStart_403433 baseEnd_403433 := by
    simpa [prefixWord, tailWord_403433, baseEnd_403433] using wordTrace_append hprefix tailTrace_403433
  have hstable : (prefixWord ++ tailWord_403433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403433).length < 2 ^ (prefixWord ++ tailWord_403433).sum := by decide
  have hdescent : baseEnd_403433 < baseStart_403433 := by decide
  rcases family_descends (prefixWord ++ tailWord_403433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403434 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 5]
def baseStart_403434 : Nat := 118140960795 + 403434 * 2 ^ 59
def prefixEnd_403434 : Nat := 4983230072969 + 3 ^ 40 * 403434 * 2
def baseEnd_403434 : Nat := 23017283818453310702183

theorem tailTrace_403434 : CollatzResearch.WordTrace tailWord_403434 prefixEnd_403434 23017283818453310702183 := by
  unfold tailWord_403434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3678611705108748471704339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9809631213623329257878237 3678611705108748471704339)
  ·
    refine ⟨5517917557663122707556509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3678611705108748471704339 5517917557663122707556509)
    ·
      refine ⟨2069219084123671015333691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5517917557663122707556509 2069219084123671015333691)
      ·
        refine ⟨3103828626185506523000537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069219084123671015333691 3103828626185506523000537)
        ·
          refine ⟨2327871469639129892250403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3103828626185506523000537 2327871469639129892250403)
          ·
            refine ⟨3491807204458694838375605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2327871469639129892250403 3491807204458694838375605)
            ·
              refine ⟨327356925418002641097713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3491807204458694838375605 327356925418002641097713)
              ·
                refine ⟨245517694063501980823285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327356925418002641097713 245517694063501980823285)
                ·
                  refine ⟨23017283818453310702183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245517694063501980823285 23017283818453310702183)
                  ·
                    rfl

theorem cell23_403434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 5].length) (baseStart_403434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403434 prefixEnd_403434 := by exact prefixLift 403434
  have htrace : WordTrace (prefixWord ++ tailWord_403434) baseStart_403434 baseEnd_403434 := by
    simpa [prefixWord, tailWord_403434, baseEnd_403434] using wordTrace_append hprefix tailTrace_403434
  have hstable : (prefixWord ++ tailWord_403434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403434).length < 2 ^ (prefixWord ++ tailWord_403434).sum := by decide
  have hdescent : baseEnd_403434 < baseStart_403434 := by decide
  rcases family_descends (prefixWord ++ tailWord_403434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403467 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4]
def baseStart_403467 : Nat := 118140960795 + 403467 * 2 ^ 59
def prefixEnd_403467 : Nat := 4983230072969 + 3 ^ 40 * 403467 * 2
def baseEnd_403467 : Nat := 207172499227678167206995

theorem tailTrace_403467 : CollatzResearch.WordTrace tailWord_403467 prefixEnd_403467 207172499227678167206995 := by
  unfold tailWord_403467
  simp only [CollatzResearch.WordTrace]
  refine ⟨14715650429315440522768655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9810433619543627015179103 14715650429315440522768655)
  ·
    refine ⟨22073475643973160784152983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14715650429315440522768655 22073475643973160784152983)
    ·
      refine ⟨33110213465959741176229475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22073475643973160784152983 33110213465959741176229475)
      ·
        refine ⟨49665320198939611764344213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33110213465959741176229475 49665320198939611764344213)
        ·
          refine ⟨2328061884325294301453635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49665320198939611764344213 2328061884325294301453635)
          ·
            refine ⟨3492092826487941452180453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328061884325294301453635 3492092826487941452180453)
            ·
              refine ⟨654767404966489022283835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3492092826487941452180453 654767404966489022283835)
              ·
                refine ⟨982151107449733533425753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654767404966489022283835 982151107449733533425753)
                ·
                  refine ⟨736613330587300150069315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982151107449733533425753 736613330587300150069315)
                  ·
                    refine ⟨1104919995880950225103973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 736613330587300150069315 1104919995880950225103973)
                    ·
                      refine ⟨207172499227678167206995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1104919995880950225103973 207172499227678167206995)
                      ·
                        rfl

theorem cell23_403467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4].length) (baseStart_403467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403467 prefixEnd_403467 := by exact prefixLift 403467
  have htrace : WordTrace (prefixWord ++ tailWord_403467) baseStart_403467 baseEnd_403467 := by
    simpa [prefixWord, tailWord_403467, baseEnd_403467] using wordTrace_append hprefix tailTrace_403467
  have hstable : (prefixWord ++ tailWord_403467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403467).length < 2 ^ (prefixWord ++ tailWord_403467).sum := by decide
  have hdescent : baseEnd_403467 < baseStart_403467 := by decide
  rcases family_descends (prefixWord ++ tailWord_403467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403480 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6]
def baseStart_403480 : Nat := 118140960795 + 403480 * 2 ^ 59
def prefixEnd_403480 : Nat := 4983230072969 + 3 ^ 40 * 403480 * 2
def baseEnd_403480 : Nat := 207179174476186616344435

theorem tailTrace_403480 : CollatzResearch.WordTrace tailWord_403480 prefixEnd_403480 207179174476186616344435 := by
  unfold tailWord_403480
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358062289134171871495947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9810749718845562495327929 7358062289134171871495947)
  ·
    refine ⟨11037093433701257807243921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7358062289134171871495947 11037093433701257807243921)
    ·
      refine ⟨8277820075275943355432941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11037093433701257807243921 8277820075275943355432941)
      ·
        refine ⟨3104182528228478758287353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8277820075275943355432941 3104182528228478758287353)
        ·
          refine ⟨2328136896171359068715515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104182528228478758287353 2328136896171359068715515)
          ·
            refine ⟨3492205344257038603073273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328136896171359068715515 3492205344257038603073273)
            ·
              refine ⟨2619154008192778952304955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3492205344257038603073273 2619154008192778952304955)
              ·
                refine ⟨3928731012289168428457433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2619154008192778952304955 3928731012289168428457433)
                ·
                  refine ⟨2946548259216876321343075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3928731012289168428457433 2946548259216876321343075)
                  ·
                    refine ⟨4419822388825314482014613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2946548259216876321343075 4419822388825314482014613)
                    ·
                      refine ⟨207179174476186616344435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4419822388825314482014613 207179174476186616344435)
                      ·
                        rfl

theorem cell23_403480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_403480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403480 prefixEnd_403480 := by exact prefixLift 403480
  have htrace : WordTrace (prefixWord ++ tailWord_403480) baseStart_403480 baseEnd_403480 := by
    simpa [prefixWord, tailWord_403480, baseEnd_403480] using wordTrace_append hprefix tailTrace_403480
  have hstable : (prefixWord ++ tailWord_403480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403480).length < 2 ^ (prefixWord ++ tailWord_403480).sum := by decide
  have hdescent : baseEnd_403480 < baseStart_403480 := by decide
  rcases family_descends (prefixWord ++ tailWord_403480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403487 : List Nat := [1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_403487 : Nat := 118140960795 + 403487 * 2 ^ 59
def prefixEnd_403487 : Nat := 4983230072969 + 3 ^ 40 * 403487 * 2
def baseEnd_403487 : Nat := 207182768840768088956903

theorem tailTrace_403487 : CollatzResearch.WordTrace tailWord_403487 prefixEnd_403487 207182768840768088956903 := by
  unfold tailWord_403487
  simp only [CollatzResearch.WordTrace]
  refine ⟨14716379889242983938496715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9810919926161989292331143 14716379889242983938496715)
  ·
    refine ⟨22074569833864475907745073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14716379889242983938496715 22074569833864475907745073)
    ·
      refine ⟨16555927375398356930808805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22074569833864475907745073 16555927375398356930808805)
      ·
        refine ⟨3104236382887191924526651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16555927375398356930808805 3104236382887191924526651)
        ·
          refine ⟨4656354574330787886789977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104236382887191924526651 4656354574330787886789977)
          ·
            refine ⟨3492265930748090915092483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4656354574330787886789977 3492265930748090915092483)
            ·
              refine ⟨5238398896122136372638725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3492265930748090915092483 5238398896122136372638725)
              ·
                refine ⟨982199793022900569869761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5238398896122136372638725 982199793022900569869761)
                ·
                  refine ⟨736649844767175427402321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982199793022900569869761 736649844767175427402321)
                  ·
                    refine ⟨552487383575381570551741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736649844767175427402321 552487383575381570551741)
                    ·
                      refine ⟨207182768840768088956903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552487383575381570551741 207182768840768088956903)
                      ·
                        rfl

theorem cell23_403487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_403487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403487 prefixEnd_403487 := by exact prefixLift 403487
  have htrace : WordTrace (prefixWord ++ tailWord_403487) baseStart_403487 baseEnd_403487 := by
    simpa [prefixWord, tailWord_403487, baseEnd_403487] using wordTrace_append hprefix tailTrace_403487
  have hstable : (prefixWord ++ tailWord_403487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403487).length < 2 ^ (prefixWord ++ tailWord_403487).sum := by decide
  have hdescent : baseEnd_403487 < baseStart_403487 := by decide
  rcases family_descends (prefixWord ++ tailWord_403487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403518 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_403518 : Nat := 118140960795 + 403518 * 2 ^ 59
def prefixEnd_403518 : Nat := 4983230072969 + 3 ^ 40 * 403518 * 2
def baseEnd_403518 : Nat := 207198686741057467669261

theorem tailTrace_403518 : CollatzResearch.WordTrace tailWord_403518 prefixEnd_403518 207198686741057467669261 := by
  unfold tailWord_403518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1839688819016334529109401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9811673701420450821916805 1839688819016334529109401)
  ·
    refine ⟨1379766614262250896832051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1839688819016334529109401 1379766614262250896832051)
    ·
      refine ⟨2069649921393376345248077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1379766614262250896832051 2069649921393376345248077)
      ·
        refine ⟨776118720522516129468029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2069649921393376345248077 776118720522516129468029)
        ·
          refine ⟨291044520195943548550511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 776118720522516129468029 291044520195943548550511)
          ·
            refine ⟨436566780293915322825767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291044520195943548550511 436566780293915322825767)
            ·
              refine ⟨654850170440872984238651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436566780293915322825767 654850170440872984238651)
              ·
                refine ⟨982275255661309476357977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654850170440872984238651 982275255661309476357977)
                ·
                  refine ⟨736706441745982107268483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982275255661309476357977 736706441745982107268483)
                  ·
                    refine ⟨1105059662618973160902725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 736706441745982107268483 1105059662618973160902725)
                    ·
                      refine ⟨207198686741057467669261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1105059662618973160902725 207198686741057467669261)
                      ·
                        rfl

theorem cell23_403518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_403518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403518 prefixEnd_403518 := by exact prefixLift 403518
  have htrace : WordTrace (prefixWord ++ tailWord_403518) baseStart_403518 baseEnd_403518 := by
    simpa [prefixWord, tailWord_403518, baseEnd_403518] using wordTrace_append hprefix tailTrace_403518
  have hstable : (prefixWord ++ tailWord_403518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403518).length < 2 ^ (prefixWord ++ tailWord_403518).sum := by decide
  have hdescent : baseEnd_403518 < baseStart_403518 := by decide
  rcases family_descends (prefixWord ++ tailWord_403518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403521 : List Nat := [1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_403521 : Nat := 118140960795 + 403521 * 2 ^ 59
def prefixEnd_403521 : Nat := 4983230072969 + 3 ^ 40 * 403521 * 2
def baseEnd_403521 : Nat := 207200227183020955931747

theorem tailTrace_403521 : CollatzResearch.WordTrace tailWord_403521 prefixEnd_403521 207200227183020955931747 := by
  unfold tailWord_403521
  simp only [CollatzResearch.WordTrace]
  refine ⟨14717619971119807745234417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9811746647413205163489611 14717619971119807745234417)
  ·
    refine ⟨11038214978339855808925813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14717619971119807745234417 11038214978339855808925813)
    ·
      refine ⟨1034832654219361482086795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11038214978339855808925813 1034832654219361482086795)
      ·
        refine ⟨1552248981329042223130193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034832654219361482086795 1552248981329042223130193)
        ·
          refine ⟨1164186735996781667347645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1552248981329042223130193 1164186735996781667347645)
          ·
            refine ⟨436570025998793125255367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164186735996781667347645 436570025998793125255367)
            ·
              refine ⟨654855038998189687883051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436570025998793125255367 654855038998189687883051)
              ·
                refine ⟨982282558497284531824577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654855038998189687883051 982282558497284531824577)
                ·
                  refine ⟨736711918872963398868433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982282558497284531824577 736711918872963398868433)
                  ·
                    refine ⟨552533939154722549151325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 736711918872963398868433 552533939154722549151325)
                    ·
                      refine ⟨207200227183020955931747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552533939154722549151325 207200227183020955931747)
                      ·
                        rfl

theorem cell23_403521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_403521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403521 prefixEnd_403521 := by exact prefixLift 403521
  have htrace : WordTrace (prefixWord ++ tailWord_403521) baseStart_403521 baseEnd_403521 := by
    simpa [prefixWord, tailWord_403521, baseEnd_403521] using wordTrace_append hprefix tailTrace_403521
  have hstable : (prefixWord ++ tailWord_403521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403521).length < 2 ^ (prefixWord ++ tailWord_403521).sum := by decide
  have hdescent : baseEnd_403521 < baseStart_403521 := by decide
  rcases family_descends (prefixWord ++ tailWord_403521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403530 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_403530 : Nat := 118140960795 + 403530 * 2 ^ 59
def prefixEnd_403530 : Nat := 4983230072969 + 3 ^ 40 * 403530 * 2
def baseEnd_403530 : Nat := 207204848508911420719205

theorem tailTrace_403530 : CollatzResearch.WordTrace tailWord_403530 prefixEnd_403530 207204848508911420719205 := by
  unfold tailWord_403530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679487057021800570578011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9811965485391468188208029 3679487057021800570578011)
  ·
    refine ⟨5519230585532700855867017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679487057021800570578011 5519230585532700855867017)
    ·
      refine ⟨4139422939149525641900263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5519230585532700855867017 4139422939149525641900263)
      ·
        refine ⟨6209134408724288462850395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4139422939149525641900263 6209134408724288462850395)
        ·
          refine ⟨9313701613086432694275593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6209134408724288462850395 9313701613086432694275593)
          ·
            refine ⟨6985276209814824520706695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9313701613086432694275593 6985276209814824520706695)
            ·
              refine ⟨10477914314722236781060043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6985276209814824520706695 10477914314722236781060043)
              ·
                refine ⟨15716871472083355171590065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10477914314722236781060043 15716871472083355171590065)
                ·
                  refine ⟨11787653604062516378692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15716871472083355171590065 11787653604062516378692549)
                  ·
                    refine ⟨2210185050761721821004853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11787653604062516378692549 2210185050761721821004853)
                    ·
                      refine ⟨207204848508911420719205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2210185050761721821004853 207204848508911420719205)
                      ·
                        rfl

theorem cell23_403530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_403530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403530 prefixEnd_403530 := by exact prefixLift 403530
  have htrace : WordTrace (prefixWord ++ tailWord_403530) baseStart_403530 baseEnd_403530 := by
    simpa [prefixWord, tailWord_403530, baseEnd_403530] using wordTrace_append hprefix tailTrace_403530
  have hstable : (prefixWord ++ tailWord_403530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403530).length < 2 ^ (prefixWord ++ tailWord_403530).sum := by decide
  have hdescent : baseEnd_403530 < baseStart_403530 := by decide
  rcases family_descends (prefixWord ++ tailWord_403530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403567 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 1, 6]
def baseStart_403567 : Nat := 118140960795 + 403567 * 2 ^ 59
def prefixEnd_403567 : Nat := 4983230072969 + 3 ^ 40 * 403567 * 2
def baseEnd_403567 : Nat := 69074615764375925318845

theorem tailTrace_403567 : CollatzResearch.WordTrace tailWord_403567 prefixEnd_403567 69074615764375925318845 := by
  unfold tailWord_403567
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719297728953157601408955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9812865152635438400939303 14719297728953157601408955)
  ·
    refine ⟨22078946593429736402113433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14719297728953157601408955 22078946593429736402113433)
    ·
      refine ⟨16559209945072302301585075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22078946593429736402113433 16559209945072302301585075)
      ·
        refine ⟨24838814917608453452377613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16559209945072302301585075 24838814917608453452377613)
        ·
          refine ⟨9314555594103170044641605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24838814917608453452377613 9314555594103170044641605)
          ·
            refine ⟨1746479173894344383370301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9314555594103170044641605 1746479173894344383370301)
            ·
              refine ⟨654929690210379143763863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746479173894344383370301 654929690210379143763863)
              ·
                refine ⟨982394535315568715645795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654929690210379143763863 982394535315568715645795)
                ·
                  refine ⟨1473591802973353073468693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982394535315568715645795 1473591802973353073468693)
                  ·
                    refine ⟨69074615764375925318845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1473591802973353073468693 69074615764375925318845)
                    ·
                      rfl

theorem cell23_403567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_403567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403567 prefixEnd_403567 := by exact prefixLift 403567
  have htrace : WordTrace (prefixWord ++ tailWord_403567) baseStart_403567 baseEnd_403567 := by
    simpa [prefixWord, tailWord_403567, baseEnd_403567] using wordTrace_append hprefix tailTrace_403567
  have hstable : (prefixWord ++ tailWord_403567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403567).length < 2 ^ (prefixWord ++ tailWord_403567).sum := by decide
  have hdescent : baseEnd_403567 < baseStart_403567 := by decide
  rcases family_descends (prefixWord ++ tailWord_403567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403585 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_403585 : Nat := 118140960795 + 403585 * 2 ^ 59
def prefixEnd_403585 : Nat := 4983230072969 + 3 ^ 40 * 403585 * 2
def baseEnd_403585 : Nat := 207233089944908705531453

theorem tailTrace_403585 : CollatzResearch.WordTrace tailWord_403585 prefixEnd_403585 207233089944908705531453 := by
  unfold tailWord_403585
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719954242887946675564209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9813302828591964450376139 14719954242887946675564209)
  ·
    refine ⟨11039965682165960006673157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14719954242887946675564209 11039965682165960006673157)
    ·
      refine ⟨2069993565406117501251217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11039965682165960006673157 2069993565406117501251217)
      ·
        refine ⟨1552495174054588125938413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2069993565406117501251217 1552495174054588125938413)
        ·
          refine ⟨582185690270470547226905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1552495174054588125938413 582185690270470547226905)
          ·
            refine ⟨436639267702852910420179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582185690270470547226905 436639267702852910420179)
            ·
              refine ⟨654958901554279365630269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436639267702852910420179 654958901554279365630269)
              ·
                refine ⟨245609588082854762111351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654958901554279365630269 245609588082854762111351)
                ·
                  refine ⟨368414382124282143167027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245609588082854762111351 368414382124282143167027)
                  ·
                    refine ⟨552621573186423214750541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 368414382124282143167027 552621573186423214750541)
                    ·
                      refine ⟨207233089944908705531453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552621573186423214750541 207233089944908705531453)
                      ·
                        rfl

theorem cell23_403585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_403585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403585 prefixEnd_403585 := by exact prefixLift 403585
  have htrace : WordTrace (prefixWord ++ tailWord_403585) baseStart_403585 baseEnd_403585 := by
    simpa [prefixWord, tailWord_403585, baseEnd_403585] using wordTrace_append hprefix tailTrace_403585
  have hstable : (prefixWord ++ tailWord_403585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403585).length < 2 ^ (prefixWord ++ tailWord_403585).sum := by decide
  have hdescent : baseEnd_403585 < baseStart_403585 := by decide
  rcases family_descends (prefixWord ++ tailWord_403585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403594 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_403594 : Nat := 118140960795 + 403594 * 2 ^ 59
def prefixEnd_403594 : Nat := 4983230072969 + 3 ^ 40 * 403594 * 2
def baseEnd_403594 : Nat := 207237711270799170318911

theorem tailTrace_403594 : CollatzResearch.WordTrace tailWord_403594 prefixEnd_403594 207237711270799170318911 := by
  unfold tailWord_403594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680070624963835303160459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9813521666570227475094557 3680070624963835303160459)
  ·
    refine ⟨5520105937445752954740689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680070624963835303160459 5520105937445752954740689)
    ·
      refine ⟨4140079453084314716055517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5520105937445752954740689 4140079453084314716055517)
      ·
        refine ⟨1552529794906618018520819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4140079453084314716055517 1552529794906618018520819)
        ·
          refine ⟨2328794692359927027781229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552529794906618018520819 2328794692359927027781229)
          ·
            refine ⟨873298009634972635417961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2328794692359927027781229 873298009634972635417961)
            ·
              refine ⟨654973507226229476563471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873298009634972635417961 654973507226229476563471)
              ·
                refine ⟨982460260839344214845207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654973507226229476563471 982460260839344214845207)
                ·
                  refine ⟨1473690391259016322267811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982460260839344214845207 1473690391259016322267811)
                  ·
                    refine ⟨2210535586888524483401717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1473690391259016322267811 2210535586888524483401717)
                    ·
                      refine ⟨207237711270799170318911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2210535586888524483401717 207237711270799170318911)
                      ·
                        rfl

theorem cell23_403594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_403594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403594 prefixEnd_403594 := by exact prefixLift 403594
  have htrace : WordTrace (prefixWord ++ tailWord_403594) baseStart_403594 baseEnd_403594 := by
    simpa [prefixWord, tailWord_403594, baseEnd_403594] using wordTrace_append hprefix tailTrace_403594
  have hstable : (prefixWord ++ tailWord_403594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403594).length < 2 ^ (prefixWord ++ tailWord_403594).sum := by decide
  have hdescent : baseEnd_403594 < baseStart_403594 := by decide
  rcases family_descends (prefixWord ++ tailWord_403594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403618 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_403618 : Nat := 118140960795 + 403618 * 2 ^ 59
def prefixEnd_403618 : Nat := 4983230072969 + 3 ^ 40 * 403618 * 2
def baseEnd_403618 : Nat := 69083344935502358806267

theorem tailTrace_403618 : CollatzResearch.WordTrace tailWord_403618 prefixEnd_403618 69083344935502358806267 := by
  unfold tailWord_403618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680289462942098327878877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9814105234512262207677005 3680289462942098327878877)
  ·
    refine ⟨1380108548603286872954579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3680289462942098327878877 1380108548603286872954579)
    ·
      refine ⟨2070162822904930309431869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380108548603286872954579 2070162822904930309431869)
      ·
        refine ⟨776311058589348866036951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2070162822904930309431869 776311058589348866036951)
        ·
          refine ⟨1164466587884023299055427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776311058589348866036951 1164466587884023299055427)
          ·
            refine ⟨1746699881826034948583141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164466587884023299055427 1746699881826034948583141)
            ·
              refine ⟨327506227842381552859339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1746699881826034948583141 327506227842381552859339)
              ·
                refine ⟨491259341763572329289009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327506227842381552859339 491259341763572329289009)
                ·
                  refine ⟨368444506322679246966757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 491259341763572329289009 368444506322679246966757)
                  ·
                    refine ⟨69083344935502358806267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368444506322679246966757 69083344935502358806267)
                    ·
                      rfl

theorem cell23_403618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_403618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403618 prefixEnd_403618 := by exact prefixLift 403618
  have htrace : WordTrace (prefixWord ++ tailWord_403618) baseStart_403618 baseEnd_403618 := by
    simpa [prefixWord, tailWord_403618, baseEnd_403618] using wordTrace_append hprefix tailTrace_403618
  have hstable : (prefixWord ++ tailWord_403618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403618).length < 2 ^ (prefixWord ++ tailWord_403618).sum := by decide
  have hdescent : baseEnd_403618 < baseStart_403618 := by decide
  rcases family_descends (prefixWord ++ tailWord_403618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403681 : List Nat := [1, 2, 3, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_403681 : Nat := 118140960795 + 403681 * 2 ^ 59
def prefixEnd_403681 : Nat := 4983230072969 + 3 ^ 40 * 403681 * 2
def baseEnd_403681 : Nat := 207282384087740329931011

theorem tailTrace_403681 : CollatzResearch.WordTrace tailWord_403681 prefixEnd_403681 207282384087740329931011 := by
  unfold tailWord_403681
  simp only [CollatzResearch.WordTrace]
  refine ⟨14723455650540155071058897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9815637100360103380705931 14723455650540155071058897)
  ·
    refine ⟨11042591737905116303294173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14723455650540155071058897 11042591737905116303294173)
    ·
      refine ⟨4140971901714418613735315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11042591737905116303294173 4140971901714418613735315)
      ·
        refine ⟨6211457852571627920602973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4140971901714418613735315 6211457852571627920602973)
        ·
          refine ⟨2329296694714360470226115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6211457852571627920602973 2329296694714360470226115)
          ·
            refine ⟨3493945042071540705339173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329296694714360470226115 3493945042071540705339173)
            ·
              refine ⟨655114695388413882251095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3493945042071540705339173 655114695388413882251095)
              ·
                refine ⟨982672043082620823376643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655114695388413882251095 982672043082620823376643)
                ·
                  refine ⟨1474008064623931235064965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 982672043082620823376643 1474008064623931235064965)
                  ·
                    refine ⟨276376512116987106574681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1474008064623931235064965 276376512116987106574681)
                    ·
                      refine ⟨207282384087740329931011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276376512116987106574681 207282384087740329931011)
                      ·
                        rfl

theorem cell23_403681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_403681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403681 prefixEnd_403681 := by exact prefixLift 403681
  have htrace : WordTrace (prefixWord ++ tailWord_403681) baseStart_403681 baseEnd_403681 := by
    simpa [prefixWord, tailWord_403681, baseEnd_403681] using wordTrace_append hprefix tailTrace_403681
  have hstable : (prefixWord ++ tailWord_403681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403681).length < 2 ^ (prefixWord ++ tailWord_403681).sum := by decide
  have hdescent : baseEnd_403681 < baseStart_403681 := by decide
  rcases family_descends (prefixWord ++ tailWord_403681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403727 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_403727 : Nat := 118140960795 + 403727 * 2 ^ 59
def prefixEnd_403727 : Nat := 4983230072969 + 3 ^ 40 * 403727 * 2
def baseEnd_403727 : Nat := 207306004197847149955799

theorem tailTrace_403727 : CollatzResearch.WordTrace tailWord_403727 prefixEnd_403727 207306004197847149955799 := by
  unfold tailWord_403727
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725133408373504927233435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9816755605582336618155623 14725133408373504927233435)
  ·
    refine ⟨22087700112560257390850153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725133408373504927233435 22087700112560257390850153)
    ·
      refine ⟨16565775084420193043137615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22087700112560257390850153 16565775084420193043137615)
      ·
        refine ⟨24848662626630289564706423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16565775084420193043137615 24848662626630289564706423)
        ·
          refine ⟨37272993939945434347059635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24848662626630289564706423 37272993939945434347059635)
          ·
            refine ⟨55909490909918151520589453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37272993939945434347059635 55909490909918151520589453)
            ·
              refine ⟨20966059091219306820221045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55909490909918151520589453 20966059091219306820221045)
              ·
                refine ⟨1965568039801810014395723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20966059091219306820221045 1965568039801810014395723)
                ·
                  refine ⟨2948352059702715021593585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1965568039801810014395723 2948352059702715021593585)
                  ·
                    refine ⟨2211264044777036266195189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2948352059702715021593585 2211264044777036266195189)
                    ·
                      refine ⟨207306004197847149955799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2211264044777036266195189 207306004197847149955799)
                      ·
                        rfl

theorem cell23_403727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_403727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403727 prefixEnd_403727 := by exact prefixLift 403727
  have htrace : WordTrace (prefixWord ++ tailWord_403727) baseStart_403727 baseEnd_403727 := by
    simpa [prefixWord, tailWord_403727, baseEnd_403727] using wordTrace_append hprefix tailTrace_403727
  have hstable : (prefixWord ++ tailWord_403727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403727).length < 2 ^ (prefixWord ++ tailWord_403727).sum := by decide
  have hdescent : baseEnd_403727 < baseStart_403727 := by decide
  rcases family_descends (prefixWord ++ tailWord_403727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403747 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 8]
def baseStart_403747 : Nat := 118140960795 + 403747 * 2 ^ 59
def prefixEnd_403747 : Nat := 4983230072969 + 3 ^ 40 * 403747 * 2
def baseEnd_403747 : Nat := 69105424603645690568569

theorem tailTrace_403747 : CollatzResearch.WordTrace tailWord_403747 prefixEnd_403747 69105424603645690568569 := by
  unfold tailWord_403747
  simp only [CollatzResearch.WordTrace]
  refine ⟨14725862868301048342961495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9817241912200698895307663 14725862868301048342961495)
  ·
    refine ⟨22088794302451572514442243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14725862868301048342961495 22088794302451572514442243)
    ·
      refine ⟨33133191453677358771663365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22088794302451572514442243 33133191453677358771663365)
      ·
        refine ⟨6212473397564504769686881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33133191453677358771663365 6212473397564504769686881)
        ·
          refine ⟨4659355048173378577265161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6212473397564504769686881 4659355048173378577265161)
          ·
            refine ⟨3494516286130033932948871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4659355048173378577265161 3494516286130033932948871)
            ·
              refine ⟨5241774429195050899423307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3494516286130033932948871 5241774429195050899423307)
              ·
                refine ⟨7862661643792576349134961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5241774429195050899423307 7862661643792576349134961)
                ·
                  refine ⟨5896996232844432261851221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7862661643792576349134961 5896996232844432261851221)
                  ·
                    refine ⟨69105424603645690568569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5896996232844432261851221 69105424603645690568569)
                    ·
                      rfl

theorem cell23_403747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_403747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403747 prefixEnd_403747 := by exact prefixLift 403747
  have htrace : WordTrace (prefixWord ++ tailWord_403747) baseStart_403747 baseEnd_403747 := by
    simpa [prefixWord, tailWord_403747, baseEnd_403747] using wordTrace_append hprefix tailTrace_403747
  have hstable : (prefixWord ++ tailWord_403747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403747).length < 2 ^ (prefixWord ++ tailWord_403747).sum := by decide
  have hdescent : baseEnd_403747 < baseStart_403747 := by decide
  rcases family_descends (prefixWord ++ tailWord_403747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403767 : List Nat := [1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_403767 : Nat := 118140960795 + 403767 * 2 ^ 59
def prefixEnd_403767 : Nat := 4983230072969 + 3 ^ 40 * 403767 * 2
def baseEnd_403767 : Nat := 207326543424026993455615

theorem tailTrace_403767 : CollatzResearch.WordTrace tailWord_403767 prefixEnd_403767 207326543424026993455615 := by
  unfold tailWord_403767
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726592328228591758689555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9817728218819061172459703 14726592328228591758689555)
  ·
    refine ⟨22089888492342887638034333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14726592328228591758689555 22089888492342887638034333)
    ·
      refine ⟨8283708184628582864262875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22089888492342887638034333 8283708184628582864262875)
      ·
        refine ⟨12425562276942874296394313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8283708184628582864262875 12425562276942874296394313)
        ·
          refine ⟨9319171707707155722295735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12425562276942874296394313 9319171707707155722295735)
          ·
            refine ⟨13978757561560733583443603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9319171707707155722295735 13978757561560733583443603)
            ·
              refine ⟨20968136342341100375165405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13978757561560733583443603 20968136342341100375165405)
              ·
                refine ⟨7863051128377912640687027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20968136342341100375165405 7863051128377912640687027)
                ·
                  refine ⟨11794576692566868961030541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7863051128377912640687027 11794576692566868961030541)
                  ·
                    refine ⟨4422966259712575860386453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11794576692566868961030541 4422966259712575860386453)
                    ·
                      refine ⟨207326543424026993455615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4422966259712575860386453 207326543424026993455615)
                      ·
                        rfl

theorem cell23_403767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_403767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403767 prefixEnd_403767 := by exact prefixLift 403767
  have htrace : WordTrace (prefixWord ++ tailWord_403767) baseStart_403767 baseEnd_403767 := by
    simpa [prefixWord, tailWord_403767, baseEnd_403767] using wordTrace_append hprefix tailTrace_403767
  have hstable : (prefixWord ++ tailWord_403767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403767).length < 2 ^ (prefixWord ++ tailWord_403767).sum := by decide
  have hdescent : baseEnd_403767 < baseStart_403767 := by decide
  rcases family_descends (prefixWord ++ tailWord_403767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403808 : List Nat := [2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3]
def baseStart_403808 : Nat := 118140960795 + 403808 * 2 ^ 59
def prefixEnd_403808 : Nat := 4983230072969 + 3 ^ 40 * 403808 * 2
def baseEnd_403808 : Nat := 207347596130861333042927

theorem tailTrace_403808 : CollatzResearch.WordTrace tailWord_403808 prefixEnd_403808 207347596130861333042927 := by
  unfold tailWord_403808
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364043860540027880466039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9818725147386703840621385 7364043860540027880466039)
  ·
    refine ⟨11046065790810041820699059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7364043860540027880466039 11046065790810041820699059)
    ·
      refine ⟨16569098686215062731048589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11046065790810041820699059 16569098686215062731048589)
      ·
        refine ⟨6213412007330648524143221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16569098686215062731048589 6213412007330648524143221)
        ·
          refine ⟨582507375687248299138427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6213412007330648524143221 582507375687248299138427)
          ·
            refine ⟨873761063530872448707641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582507375687248299138427 873761063530872448707641)
            ·
              refine ⟨655320797648154336530731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873761063530872448707641 655320797648154336530731)
              ·
                refine ⟨982981196472231504796097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655320797648154336530731 982981196472231504796097)
                ·
                  refine ⟨737235897354173628597073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 982981196472231504796097 737235897354173628597073)
                  ·
                    refine ⟨552926923015630221447805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 737235897354173628597073 552926923015630221447805)
                    ·
                      refine ⟨207347596130861333042927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 552926923015630221447805 207347596130861333042927)
                      ·
                        rfl

theorem cell23_403808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_403808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403808 prefixEnd_403808 := by exact prefixLift 403808
  have htrace : WordTrace (prefixWord ++ tailWord_403808) baseStart_403808 baseEnd_403808 := by
    simpa [prefixWord, tailWord_403808, baseEnd_403808] using wordTrace_append hprefix tailTrace_403808
  have hstable : (prefixWord ++ tailWord_403808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403808).length < 2 ^ (prefixWord ++ tailWord_403808).sum := by decide
  have hdescent : baseEnd_403808 < baseStart_403808 := by decide
  rcases family_descends (prefixWord ++ tailWord_403808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403831 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_403831 : Nat := 118140960795 + 403831 * 2 ^ 59
def prefixEnd_403831 : Nat := 4983230072969 + 3 ^ 40 * 403831 * 2
def baseEnd_403831 : Nat := 207359406185914743055321

theorem tailTrace_403831 : CollatzResearch.WordTrace tailWord_403831 prefixEnd_403831 207359406185914743055321 := by
  unfold tailWord_403831
  simp only [CollatzResearch.WordTrace]
  refine ⟨14728926599996730689019347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9819284399997820459346231 14728926599996730689019347)
  ·
    refine ⟨22093389899995096033529021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14728926599996730689019347 22093389899995096033529021)
    ·
      refine ⟨8285021212498161012573383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22093389899995096033529021 8285021212498161012573383)
      ·
        refine ⟨12427531818747241518860075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8285021212498161012573383 12427531818747241518860075)
        ·
          refine ⟨18641297728120862278290113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12427531818747241518860075 18641297728120862278290113)
          ·
            refine ⟨13980973296090646708717585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18641297728120862278290113 13980973296090646708717585)
            ·
              refine ⟨10485729972067985031538189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13980973296090646708717585 10485729972067985031538189)
              ·
                refine ⟨3932148739525494386826821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10485729972067985031538189 3932148739525494386826821)
                ·
                  refine ⟨737277888661030197530029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3932148739525494386826821 737277888661030197530029)
                  ·
                    refine ⟨276479208247886324073761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737277888661030197530029 276479208247886324073761)
                    ·
                      refine ⟨207359406185914743055321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276479208247886324073761 207359406185914743055321)
                      ·
                        rfl

theorem cell23_403831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_403831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403831 prefixEnd_403831 := by exact prefixLift 403831
  have htrace : WordTrace (prefixWord ++ tailWord_403831) baseStart_403831 baseEnd_403831 := by
    simpa [prefixWord, tailWord_403831, baseEnd_403831] using wordTrace_append hprefix tailTrace_403831
  have hstable : (prefixWord ++ tailWord_403831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403831).length < 2 ^ (prefixWord ++ tailWord_403831).sum := by decide
  have hdescent : baseEnd_403831 < baseStart_403831 := by decide
  rcases family_descends (prefixWord ++ tailWord_403831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403841 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 3, 5]
def baseStart_403841 : Nat := 118140960795 + 403841 * 2 ^ 59
def prefixEnd_403841 : Nat := 4983230072969 + 3 ^ 40 * 403841 * 2
def baseEnd_403841 : Nat := 69121513664153234643425

theorem tailTrace_403841 : CollatzResearch.WordTrace tailWord_403841 prefixEnd_403841 69121513664153234643425 := by
  unfold tailWord_403841
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729291329960502396883377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9819527553307001597922251 14729291329960502396883377)
  ·
    refine ⟨11046968497470376797662533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14729291329960502396883377 11046968497470376797662533)
    ·
      refine ⟨2071306593275695649561725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11046968497470376797662533 2071306593275695649561725)
      ·
        refine ⟨776739972478385868585647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2071306593275695649561725 776739972478385868585647)
        ·
          refine ⟨1165109958717578802878471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776739972478385868585647 1165109958717578802878471)
          ·
            refine ⟨1747664938076368204317707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165109958717578802878471 1747664938076368204317707)
            ·
              refine ⟨2621497407114552306476561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1747664938076368204317707 2621497407114552306476561)
              ·
                refine ⟨1966123055335914229857421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621497407114552306476561 1966123055335914229857421)
                ·
                  refine ⟨737296145750967836196533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1966123055335914229857421 737296145750967836196533)
                  ·
                    refine ⟨69121513664153234643425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 737296145750967836196533 69121513664153234643425)
                    ·
                      rfl

theorem cell23_403841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_403841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403841 prefixEnd_403841 := by exact prefixLift 403841
  have htrace : WordTrace (prefixWord ++ tailWord_403841) baseStart_403841 baseEnd_403841 := by
    simpa [prefixWord, tailWord_403841, baseEnd_403841] using wordTrace_append hprefix tailTrace_403841
  have hstable : (prefixWord ++ tailWord_403841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403841).length < 2 ^ (prefixWord ++ tailWord_403841).sum := by decide
  have hdescent : baseEnd_403841 < baseStart_403841 := by decide
  rcases family_descends (prefixWord ++ tailWord_403841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403861 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_403861 : Nat := 118140960795 + 403861 * 2 ^ 59
def prefixEnd_403861 : Nat := 4983230072969 + 3 ^ 40 * 403861 * 2
def baseEnd_403861 : Nat := 207374810605549625680183

theorem tailTrace_403861 : CollatzResearch.WordTrace tailWord_403861 prefixEnd_403861 207374810605549625680183 := by
  unfold tailWord_403861
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730020789888045812611437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9820013859925363875074291 14730020789888045812611437)
  ·
    refine ⟨5523757796208017179729289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14730020789888045812611437 5523757796208017179729289)
    ·
      refine ⟨4142818347156012884796967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5523757796208017179729289 4142818347156012884796967)
      ·
        refine ⟨6214227520734019327195451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4142818347156012884796967 6214227520734019327195451)
        ·
          refine ⟨9321341281101028990793177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6214227520734019327195451 9321341281101028990793177)
          ·
            refine ⟨6991005960825771743094883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9321341281101028990793177 6991005960825771743094883)
            ·
              refine ⟨10486508941238657614642325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991005960825771743094883 10486508941238657614642325)
              ·
                refine ⟨491555106620562075686359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10486508941238657614642325 491555106620562075686359)
                ·
                  refine ⟨737332659930843113529539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491555106620562075686359 737332659930843113529539)
                  ·
                    refine ⟨1105998989896264670294309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 737332659930843113529539 1105998989896264670294309)
                    ·
                      refine ⟨207374810605549625680183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1105998989896264670294309 207374810605549625680183)
                      ·
                        rfl

theorem cell23_403861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_403861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403861 prefixEnd_403861 := by exact prefixLift 403861
  have htrace : WordTrace (prefixWord ++ tailWord_403861) baseStart_403861 baseEnd_403861 := by
    simpa [prefixWord, tailWord_403861, baseEnd_403861] using wordTrace_append hprefix tailTrace_403861
  have hstable : (prefixWord ++ tailWord_403861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403861).length < 2 ^ (prefixWord ++ tailWord_403861).sum := by decide
  have hdescent : baseEnd_403861 < baseStart_403861 := by decide
  rcases family_descends (prefixWord ++ tailWord_403861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403871 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 4, 4]
def baseStart_403871 : Nat := 118140960795 + 403871 * 2 ^ 59
def prefixEnd_403871 : Nat := 4983230072969 + 3 ^ 40 * 403871 * 2
def baseEnd_403871 : Nat := 69126648470698195518379

theorem tailTrace_403871 : CollatzResearch.WordTrace tailWord_403871 prefixEnd_403871 69126648470698195518379 := by
  unfold tailWord_403871
  simp only [CollatzResearch.WordTrace]
  refine ⟨14730385519851817520475467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9820257013234545013650311 14730385519851817520475467)
  ·
    refine ⟨22095578279777726280713201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14730385519851817520475467 22095578279777726280713201)
    ·
      refine ⟨16571683709833294710534901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22095578279777726280713201 16571683709833294710534901)
      ·
        refine ⟨1553595347796871379112647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16571683709833294710534901 1553595347796871379112647)
        ·
          refine ⟨2330393021695307068668971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553595347796871379112647 2330393021695307068668971)
          ·
            refine ⟨3495589532542960603003457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2330393021695307068668971 3495589532542960603003457)
            ·
              refine ⟨2621692149407220452252593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3495589532542960603003457 2621692149407220452252593)
              ·
                refine ⟨1966269112055415339189445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2621692149407220452252593 1966269112055415339189445)
                ·
                  refine ⟨368675458510390376098021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1966269112055415339189445 368675458510390376098021)
                  ·
                    refine ⟨69126648470698195518379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368675458510390376098021 69126648470698195518379)
                    ·
                      rfl

theorem cell23_403871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 4, 4].length) (baseStart_403871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403871 prefixEnd_403871 := by exact prefixLift 403871
  have htrace : WordTrace (prefixWord ++ tailWord_403871) baseStart_403871 baseEnd_403871 := by
    simpa [prefixWord, tailWord_403871, baseEnd_403871] using wordTrace_append hprefix tailTrace_403871
  have hstable : (prefixWord ++ tailWord_403871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403871).length < 2 ^ (prefixWord ++ tailWord_403871).sum := by decide
  have hdescent : baseEnd_403871 < baseStart_403871 := by decide
  rcases family_descends (prefixWord ++ tailWord_403871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403895 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_403895 : Nat := 118140960795 + 403895 * 2 ^ 59
def prefixEnd_403895 : Nat := 4983230072969 + 3 ^ 40 * 403895 * 2
def baseEnd_403895 : Nat := 207392268947802492655027

theorem tailTrace_403895 : CollatzResearch.WordTrace tailWord_403895 prefixEnd_403895 207392268947802492655027 := by
  unfold tailWord_403895
  simp only [CollatzResearch.WordTrace]
  refine ⟨14731260871764869619349139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9820840581176579746232759 14731260871764869619349139)
  ·
    refine ⟨22096891307647304429023709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14731260871764869619349139 22096891307647304429023709)
    ·
      refine ⟨8286334240367739160883891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22096891307647304429023709 8286334240367739160883891)
      ·
        refine ⟨12429501360551608741325837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8286334240367739160883891 12429501360551608741325837)
        ·
          refine ⟨4661063010206853277997189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12429501360551608741325837 4661063010206853277997189)
          ·
            refine ⟨873949314413784989624473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4661063010206853277997189 873949314413784989624473)
            ·
              refine ⟨655461985810338742218355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873949314413784989624473 655461985810338742218355)
              ·
                refine ⟨983192978715508113327533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 655461985810338742218355 983192978715508113327533)
                ·
                  refine ⟨368697367018315542497825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 983192978715508113327533 368697367018315542497825)
                  ·
                    refine ⟨276523025263736656873369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 368697367018315542497825 276523025263736656873369)
                    ·
                      refine ⟨207392268947802492655027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276523025263736656873369 207392268947802492655027)
                      ·
                        rfl

theorem cell23_403895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_403895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403895 prefixEnd_403895 := by exact prefixLift 403895
  have htrace : WordTrace (prefixWord ++ tailWord_403895) baseStart_403895 baseEnd_403895 := by
    simpa [prefixWord, tailWord_403895, baseEnd_403895] using wordTrace_append hprefix tailTrace_403895
  have hstable : (prefixWord ++ tailWord_403895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403895).length < 2 ^ (prefixWord ++ tailWord_403895).sum := by decide
  have hdescent : baseEnd_403895 < baseStart_403895 := by decide
  rcases family_descends (prefixWord ++ tailWord_403895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403908 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_403908 : Nat := 118140960795 + 403908 * 2 ^ 59
def prefixEnd_403908 : Nat := 4983230072969 + 3 ^ 40 * 403908 * 2
def baseEnd_403908 : Nat := 207398944196310941792467

theorem tailTrace_403908 : CollatzResearch.WordTrace tailWord_403908 prefixEnd_403908 207398944196310941792467 := by
  unfold tailWord_403908
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365867510358886419786189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9821156680478515226381585 7365867510358886419786189)
  ·
    refine ⟨2762200316384582407419821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7365867510358886419786189 2762200316384582407419821)
    ·
      refine ⟨1035825118644218402782433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2762200316384582407419821 1035825118644218402782433)
      ·
        refine ⟨776868838983163802086825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035825118644218402782433 776868838983163802086825)
        ·
          refine ⟨582651629237372851565119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 776868838983163802086825 582651629237372851565119)
          ·
            refine ⟨873977443856059277347679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582651629237372851565119 873977443856059277347679)
            ·
              refine ⟨1310966165784088916021519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 873977443856059277347679 1310966165784088916021519)
              ·
                refine ⟨1966449248676133374032279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1310966165784088916021519 1966449248676133374032279)
                ·
                  refine ⟨2949673873014200061048419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966449248676133374032279 2949673873014200061048419)
                  ·
                    refine ⟨4424510809521300091572629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2949673873014200061048419 4424510809521300091572629)
                    ·
                      refine ⟨207398944196310941792467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4424510809521300091572629 207398944196310941792467)
                      ·
                        rfl

theorem cell23_403908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_403908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403908 prefixEnd_403908 := by exact prefixLift 403908
  have htrace : WordTrace (prefixWord ++ tailWord_403908) baseStart_403908 baseEnd_403908 := by
    simpa [prefixWord, tailWord_403908, baseEnd_403908] using wordTrace_append hprefix tailTrace_403908
  have hstable : (prefixWord ++ tailWord_403908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403908).length < 2 ^ (prefixWord ++ tailWord_403908).sum := by decide
  have hdescent : baseEnd_403908 < baseStart_403908 := by decide
  rcases family_descends (prefixWord ++ tailWord_403908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403921 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_403921 : Nat := 118140960795 + 403921 * 2 ^ 59
def prefixEnd_403921 : Nat := 4983230072969 + 3 ^ 40 * 403921 * 2
def baseEnd_403921 : Nat := 207405619444819390929907

theorem tailTrace_403921 : CollatzResearch.WordTrace tailWord_403921 prefixEnd_403921 207405619444819390929907 := by
  unfold tailWord_403921
  simp only [CollatzResearch.WordTrace]
  refine ⟨14732209169670676059795617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9821472779780450706530411 14732209169670676059795617)
  ·
    refine ⟨11049156877253007044846713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14732209169670676059795617 11049156877253007044846713)
    ·
      refine ⟨8286867657939755283635035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11049156877253007044846713 8286867657939755283635035)
      ·
        refine ⟨12430301486909632925452553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8286867657939755283635035 12430301486909632925452553)
        ·
          refine ⟨9322726115182224694089415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12430301486909632925452553 9322726115182224694089415)
          ·
            refine ⟨13984089172773337041134123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9322726115182224694089415 13984089172773337041134123)
            ·
              refine ⟨20976133759160005561701185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13984089172773337041134123 20976133759160005561701185)
              ·
                refine ⟨15732100319370004171275889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20976133759160005561701185 15732100319370004171275889)
                ·
                  refine ⟨11799075239527503128456917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15732100319370004171275889 11799075239527503128456917)
                  ·
                    refine ⟨276540825926425854573209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11799075239527503128456917 276540825926425854573209)
                    ·
                      refine ⟨207405619444819390929907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276540825926425854573209 207405619444819390929907)
                      ·
                        rfl

theorem cell23_403921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_403921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403921 prefixEnd_403921 := by exact prefixLift 403921
  have htrace : WordTrace (prefixWord ++ tailWord_403921) baseStart_403921 baseEnd_403921 := by
    simpa [prefixWord, tailWord_403921, baseEnd_403921] using wordTrace_append hprefix tailTrace_403921
  have hstable : (prefixWord ++ tailWord_403921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403921).length < 2 ^ (prefixWord ++ tailWord_403921).sum := by decide
  have hdescent : baseEnd_403921 < baseStart_403921 := by decide
  rcases family_descends (prefixWord ++ tailWord_403921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403972 : List Nat := [2, 3, 2, 3, 1, 1, 3, 2, 1, 3, 2]
def baseStart_403972 : Nat := 118140960795 + 403972 * 2 ^ 59
def prefixEnd_403972 : Nat := 4983230072969 + 3 ^ 40 * 403972 * 2
def baseEnd_403972 : Nat := 207431806958198691392173

theorem tailTrace_403972 : CollatzResearch.WordTrace tailWord_403972 prefixEnd_403972 207431806958198691392173 := by
  unfold tailWord_403972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367034646242955884951085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9822712861657274513268113 7367034646242955884951085)
  ·
    refine ⟨2762637992341108456856657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7367034646242955884951085 2762637992341108456856657)
    ·
      refine ⟨2071978494255831342642493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2762637992341108456856657 2071978494255831342642493)
      ·
        refine ⟨776991935345936753490935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2071978494255831342642493 776991935345936753490935)
        ·
          refine ⟨1165487903018905130236403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776991935345936753490935 1165487903018905130236403)
          ·
            refine ⟨1748231854528357695354605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165487903018905130236403 1748231854528357695354605)
            ·
              refine ⟨655586945448134135757977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1748231854528357695354605 655586945448134135757977)
              ·
                refine ⟨491690209086100601818483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 655586945448134135757977 491690209086100601818483)
                ·
                  refine ⟨737535313629150902727725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491690209086100601818483 737535313629150902727725)
                  ·
                    refine ⟨276575742610931588522897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 737535313629150902727725 276575742610931588522897)
                    ·
                      refine ⟨207431806958198691392173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276575742610931588522897 207431806958198691392173)
                      ·
                        rfl

theorem cell23_403972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_403972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403972 prefixEnd_403972 := by exact prefixLift 403972
  have htrace : WordTrace (prefixWord ++ tailWord_403972) baseStart_403972 baseEnd_403972 := by
    simpa [prefixWord, tailWord_403972, baseEnd_403972] using wordTrace_append hprefix tailTrace_403972
  have hstable : (prefixWord ++ tailWord_403972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403972).length < 2 ^ (prefixWord ++ tailWord_403972).sum := by decide
  have hdescent : baseEnd_403972 < baseStart_403972 := by decide
  rcases family_descends (prefixWord ++ tailWord_403972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403984 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9]
def baseStart_403984 : Nat := 118140960795 + 403984 * 2 ^ 59
def prefixEnd_403984 : Nat := 4983230072969 + 3 ^ 40 * 403984 * 2
def baseEnd_403984 : Nat := 207437968726052644442117

theorem tailTrace_403984 : CollatzResearch.WordTrace tailWord_403984 prefixEnd_403984 207437968726052644442117 := by
  unfold tailWord_403984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7367253484221218909669503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9823004645628291879559337 7367253484221218909669503)
  ·
    refine ⟨11050880226331828364504255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7367253484221218909669503 11050880226331828364504255)
    ·
      refine ⟨16576320339497742546756383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11050880226331828364504255 16576320339497742546756383)
      ·
        refine ⟨24864480509246613820134575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16576320339497742546756383 24864480509246613820134575)
        ·
          refine ⟨37296720763869920730201863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24864480509246613820134575 37296720763869920730201863)
          ·
            refine ⟨55945081145804881095302795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37296720763869920730201863 55945081145804881095302795)
            ·
              refine ⟨83917621718707321642954193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55945081145804881095302795 83917621718707321642954193)
              ·
                refine ⟨62938216289030491232215645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83917621718707321642954193 62938216289030491232215645)
                ·
                  refine ⟨23601831108386434212080867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62938216289030491232215645 23601831108386434212080867)
                  ·
                    refine ⟨35402746662579651318121301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23601831108386434212080867 35402746662579651318121301)
                    ·
                      refine ⟨207437968726052644442117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 35402746662579651318121301 207437968726052644442117)
                      ·
                        rfl

theorem cell23_403984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 9].length) (baseStart_403984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_403984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_403984 prefixEnd_403984 := by exact prefixLift 403984
  have htrace : WordTrace (prefixWord ++ tailWord_403984) baseStart_403984 baseEnd_403984 := by
    simpa [prefixWord, tailWord_403984, baseEnd_403984] using wordTrace_append hprefix tailTrace_403984
  have hstable : (prefixWord ++ tailWord_403984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403984).length < 2 ^ (prefixWord ++ tailWord_403984).sum := by decide
  have hdescent : baseEnd_403984 < baseStart_403984 := by decide
  rcases family_descends (prefixWord ++ tailWord_403984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404021 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_404021 : Nat := 118140960795 + 404021 * 2 ^ 59
def prefixEnd_404021 : Nat := 4983230072969 + 3 ^ 40 * 404021 * 2
def baseEnd_404021 : Nat := 69152322503422999893149

theorem tailTrace_404021 : CollatzResearch.WordTrace tailWord_404021 prefixEnd_404021 69152322503422999893149 := by
  unfold tailWord_404021
  simp only [CollatzResearch.WordTrace]
  refine ⟨14735856469308393138435917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9823904312872262092290611 14735856469308393138435917)
  ·
    refine ⟨5525946175990647426913469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14735856469308393138435917 5525946175990647426913469)
    ·
      refine ⟨2072229815996492785092551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5525946175990647426913469 2072229815996492785092551)
      ·
        refine ⟨3108344723994739177638827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072229815996492785092551 3108344723994739177638827)
        ·
          refine ⟨4662517085992108766458241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108344723994739177638827 4662517085992108766458241)
          ·
            refine ⟨3496887814494081574843681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4662517085992108766458241 3496887814494081574843681)
            ·
              refine ⟨2622665860870561181132761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3496887814494081574843681 2622665860870561181132761)
              ·
                refine ⟨1966999395652920885849571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2622665860870561181132761 1966999395652920885849571)
                ·
                  refine ⟨2950499093479381328774357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1966999395652920885849571 2950499093479381328774357)
                  ·
                    refine ⟨69152322503422999893149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2950499093479381328774357 69152322503422999893149)
                    ·
                      rfl

theorem cell23_404021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_404021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404021 prefixEnd_404021 := by exact prefixLift 404021
  have htrace : WordTrace (prefixWord ++ tailWord_404021) baseStart_404021 baseEnd_404021 := by
    simpa [prefixWord, tailWord_404021, baseEnd_404021] using wordTrace_append hprefix tailTrace_404021
  have hstable : (prefixWord ++ tailWord_404021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404021).length < 2 ^ (prefixWord ++ tailWord_404021).sum := by decide
  have hdescent : baseEnd_404021 < baseStart_404021 := by decide
  rcases family_descends (prefixWord ++ tailWord_404021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404071 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_404071 : Nat := 118140960795 + 404071 * 2 ^ 59
def prefixEnd_404071 : Nat := 4983230072969 + 3 ^ 40 * 404071 * 2
def baseEnd_404071 : Nat := 207482641542993804054217

theorem tailTrace_404071 : CollatzResearch.WordTrace tailWord_404071 prefixEnd_404071 207482641542993804054217 := by
  unfold tailWord_404071
  simp only [CollatzResearch.WordTrace]
  refine ⟨14737680119127251677756067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9825120079418167785170711 14737680119127251677756067)
  ·
    refine ⟨22106520178690877516634101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14737680119127251677756067 22106520178690877516634101)
    ·
      refine ⟨2072486266752269767184447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22106520178690877516634101 2072486266752269767184447)
      ·
        refine ⟨3108729400128404650776671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2072486266752269767184447 3108729400128404650776671)
        ·
          refine ⟨4663094100192606976165007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3108729400128404650776671 4663094100192606976165007)
          ·
            refine ⟨6994641150288910464247511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4663094100192606976165007 6994641150288910464247511)
            ·
              refine ⟨10491961725433365696371267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6994641150288910464247511 10491961725433365696371267)
              ·
                refine ⟨15737942588150048544556901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10491961725433365696371267 15737942588150048544556901)
                ·
                  refine ⟨2950864235278134102104419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15737942588150048544556901 2950864235278134102104419)
                  ·
                    refine ⟨4426296352917201153156629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2950864235278134102104419 4426296352917201153156629)
                    ·
                      refine ⟨207482641542993804054217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4426296352917201153156629 207482641542993804054217)
                      ·
                        rfl

theorem cell23_404071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_404071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404071 prefixEnd_404071 := by exact prefixLift 404071
  have htrace : WordTrace (prefixWord ++ tailWord_404071) baseStart_404071 baseEnd_404071 := by
    simpa [prefixWord, tailWord_404071, baseEnd_404071] using wordTrace_append hprefix tailTrace_404071
  have hstable : (prefixWord ++ tailWord_404071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404071).length < 2 ^ (prefixWord ++ tailWord_404071).sum := by decide
  have hdescent : baseEnd_404071 < baseStart_404071 := by decide
  rcases family_descends (prefixWord ++ tailWord_404071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404195 : List Nat := [1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4]
def baseStart_404195 : Nat := 118140960795 + 404195 * 2 ^ 59
def prefixEnd_404195 : Nat := 4983230072969 + 3 ^ 40 * 404195 * 2
def baseEnd_404195 : Nat := 207546313144151318903647

theorem tailTrace_404195 : CollatzResearch.WordTrace tailWord_404195 prefixEnd_404195 207546313144151318903647 := by
  unfold tailWord_404195
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742202770678020855270039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9828135180452013903513359 14742202770678020855270039)
  ·
    refine ⟨22113304156017031282905059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14742202770678020855270039 22113304156017031282905059)
    ·
      refine ⟨33169956234025546924357589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22113304156017031282905059 33169956234025546924357589)
      ·
        refine ⟨777420849234973756039631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33169956234025546924357589 777420849234973756039631)
        ·
          refine ⟨1166131273852460634059447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777420849234973756039631 1166131273852460634059447)
          ·
            refine ⟨1749196910778690951089171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166131273852460634059447 1749196910778690951089171)
            ·
              refine ⟨2623795366168036426633757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1749196910778690951089171 2623795366168036426633757)
              ·
                refine ⟨983923262313013659987659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2623795366168036426633757 983923262313013659987659)
                ·
                  refine ⟨1475884893469520489981489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 983923262313013659987659 1475884893469520489981489)
                  ·
                    refine ⟨1106913670102140367486117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1475884893469520489981489 1106913670102140367486117)
                    ·
                      refine ⟨207546313144151318903647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1106913670102140367486117 207546313144151318903647)
                      ·
                        rfl

theorem cell23_404195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_404195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404195 prefixEnd_404195 := by exact prefixLift 404195
  have htrace : WordTrace (prefixWord ++ tailWord_404195) baseStart_404195 baseEnd_404195 := by
    simpa [prefixWord, tailWord_404195, baseEnd_404195] using wordTrace_append hprefix tailTrace_404195
  have hstable : (prefixWord ++ tailWord_404195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404195).length < 2 ^ (prefixWord ++ tailWord_404195).sum := by decide
  have hdescent : baseEnd_404195 < baseStart_404195 := by decide
  rcases family_descends (prefixWord ++ tailWord_404195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404205 : List Nat := [1, 5, 1, 2, 1, 1, 5, 7]
def baseStart_404205 : Nat := 118140960795 + 404205 * 2 ^ 59
def prefixEnd_404205 : Nat := 4983230072969 + 3 ^ 40 * 404205 * 2
def baseEnd_404205 : Nat := 7687090664840602954763

theorem tailTrace_404205 : CollatzResearch.WordTrace tailWord_404205 prefixEnd_404205 7687090664840602954763 := by
  unfold tailWord_404205
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742567500641792563134069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9828378333761195042089379 14742567500641792563134069)
  ·
    refine ⟨1382115703185168052793819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14742567500641792563134069 1382115703185168052793819)
    ·
      refine ⟨2073173554777752079190729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1382115703185168052793819 2073173554777752079190729)
      ·
        refine ⟨1554880166083314059393047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2073173554777752079190729 1554880166083314059393047)
        ·
          refine ⟨2332320249124971089089571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554880166083314059393047 2332320249124971089089571)
          ·
            refine ⟨3498480373687456633634357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2332320249124971089089571 3498480373687456633634357)
            ·
              refine ⟨327982535033199059403221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3498480373687456633634357 327982535033199059403221)
              ·
                refine ⟨7687090664840602954763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 327982535033199059403221 7687090664840602954763)
                ·
                  rfl

theorem cell23_404205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 7].length) (baseStart_404205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404205 prefixEnd_404205 := by exact prefixLift 404205
  have htrace : WordTrace (prefixWord ++ tailWord_404205) baseStart_404205 baseEnd_404205 := by
    simpa [prefixWord, tailWord_404205, baseEnd_404205] using wordTrace_append hprefix tailTrace_404205
  have hstable : (prefixWord ++ tailWord_404205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404205).length < 2 ^ (prefixWord ++ tailWord_404205).sum := by decide
  have hdescent : baseEnd_404205 < baseStart_404205 := by decide
  rcases family_descends (prefixWord ++ tailWord_404205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404213 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_404213 : Nat := 118140960795 + 404213 * 2 ^ 59
def prefixEnd_404213 : Nat := 4983230072969 + 3 ^ 40 * 404213 * 2
def baseEnd_404213 : Nat := 69185185265310749492855

theorem tailTrace_404213 : CollatzResearch.WordTrace tailWord_404213 prefixEnd_404213 69185185265310749492855 := by
  unfold tailWord_404213
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742859284612809929425293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9828572856408539952950195 14742859284612809929425293)
  ·
    refine ⟨5528572231729803723534485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14742859284612809929425293 5528572231729803723534485)
    ·
      refine ⟨259151823362334549540679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5528572231729803723534485 259151823362334549540679)
      ·
        refine ⟨388727735043501824311019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259151823362334549540679 388727735043501824311019)
        ·
          refine ⟨583091602565252736466529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388727735043501824311019 583091602565252736466529)
          ·
            refine ⟨437318701923939552349897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583091602565252736466529 437318701923939552349897)
            ·
              refine ⟨327989026442954664262423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437318701923939552349897 327989026442954664262423)
              ·
                refine ⟨491983539664431996393635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327989026442954664262423 491983539664431996393635)
                ·
                  refine ⟨737975309496647994590453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 491983539664431996393635 737975309496647994590453)
                  ·
                    refine ⟨69185185265310749492855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 737975309496647994590453 69185185265310749492855)
                    ·
                      rfl

theorem cell23_404213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_404213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404213 prefixEnd_404213 := by exact prefixLift 404213
  have htrace : WordTrace (prefixWord ++ tailWord_404213) baseStart_404213 baseEnd_404213 := by
    simpa [prefixWord, tailWord_404213, baseEnd_404213] using wordTrace_append hprefix tailTrace_404213
  have hstable : (prefixWord ++ tailWord_404213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404213).length < 2 ^ (prefixWord ++ tailWord_404213).sum := by decide
  have hdescent : baseEnd_404213 < baseStart_404213 := by decide
  rcases family_descends (prefixWord ++ tailWord_404213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404215 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_404215 : Nat := 118140960795 + 404215 * 2 ^ 59
def prefixEnd_404215 : Nat := 4983230072969 + 3 ^ 40 * 404215 * 2
def baseEnd_404215 : Nat := 207556582757241240653555

theorem tailTrace_404215 : CollatzResearch.WordTrace tailWord_404215 prefixEnd_404215 207556582757241240653555 := by
  unfold tailWord_404215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14742932230605564270998099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9828621487070376180665399 14742932230605564270998099)
  ·
    refine ⟨22114398345908346406497149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14742932230605564270998099 22114398345908346406497149)
    ·
      refine ⟨8292899379715629902436431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22114398345908346406497149 8292899379715629902436431)
      ·
        refine ⟨12439349069573444853654647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8292899379715629902436431 12439349069573444853654647)
        ·
          refine ⟨18659023604360167280481971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12439349069573444853654647 18659023604360167280481971)
          ·
            refine ⟨27988535406540250920722957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18659023604360167280481971 27988535406540250920722957)
            ·
              refine ⟨10495700777452594095271109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27988535406540250920722957 10495700777452594095271109)
              ·
                refine ⟨1967943895772361392863333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10495700777452594095271109 1967943895772361392863333)
                ·
                  refine ⟨368989480457317761161875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1967943895772361392863333 368989480457317761161875)
                  ·
                    refine ⟨553484220685976641742813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 368989480457317761161875 553484220685976641742813)
                    ·
                      refine ⟨207556582757241240653555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 553484220685976641742813 207556582757241240653555)
                      ·
                        rfl

theorem cell23_404215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_404215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404215 prefixEnd_404215 := by exact prefixLift 404215
  have htrace : WordTrace (prefixWord ++ tailWord_404215) baseStart_404215 baseEnd_404215 := by
    simpa [prefixWord, tailWord_404215, baseEnd_404215] using wordTrace_append hprefix tailTrace_404215
  have hstable : (prefixWord ++ tailWord_404215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404215).length < 2 ^ (prefixWord ++ tailWord_404215).sum := by decide
  have hdescent : baseEnd_404215 < baseStart_404215 := by decide
  rcases family_descends (prefixWord ++ tailWord_404215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404232 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_404232 : Nat := 118140960795 + 404232 * 2 ^ 59
def prefixEnd_404232 : Nat := 4983230072969 + 3 ^ 40 * 404232 * 2
def baseEnd_404232 : Nat := 207565311928367674140977

theorem tailTrace_404232 : CollatzResearch.WordTrace tailWord_404232 prefixEnd_404232 207565311928367674140977 := by
  unfold tailWord_404232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7371776135771988087183475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9829034847695984116244633 7371776135771988087183475)
  ·
    refine ⟨11057664203657982130775213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7371776135771988087183475 11057664203657982130775213)
    ·
      refine ⟨4146624076371743299040705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11057664203657982130775213 4146624076371743299040705)
      ·
        refine ⟨3109968057278807474280529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4146624076371743299040705 3109968057278807474280529)
        ·
          refine ⟨2332476042959105605710397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3109968057278807474280529 2332476042959105605710397)
          ·
            refine ⟨874678516109664602141399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2332476042959105605710397 874678516109664602141399)
            ·
              refine ⟨1312017774164496903212099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874678516109664602141399 1312017774164496903212099)
              ·
                refine ⟨1968026661246745354818149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312017774164496903212099 1968026661246745354818149)
                ·
                  refine ⟨369004998983764754028403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1968026661246745354818149 369004998983764754028403)
                  ·
                    refine ⟨553507498475647131042605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369004998983764754028403 553507498475647131042605)
                    ·
                      refine ⟨207565311928367674140977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 553507498475647131042605 207565311928367674140977)
                      ·
                        rfl

theorem cell23_404232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_404232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404232 prefixEnd_404232 := by exact prefixLift 404232
  have htrace : WordTrace (prefixWord ++ tailWord_404232) baseStart_404232 baseEnd_404232 := by
    simpa [prefixWord, tailWord_404232, baseEnd_404232] using wordTrace_append hprefix tailTrace_404232
  have hstable : (prefixWord ++ tailWord_404232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404232).length < 2 ^ (prefixWord ++ tailWord_404232).sum := by decide
  have hdescent : baseEnd_404232 < baseStart_404232 := by decide
  rcases family_descends (prefixWord ++ tailWord_404232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404275 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5]
def baseStart_404275 : Nat := 118140960795 + 404275 * 2 ^ 59
def prefixEnd_404275 : Nat := 4983230072969 + 3 ^ 40 * 404275 * 2
def baseEnd_404275 : Nat := 207587391596511005903279

theorem tailTrace_404275 : CollatzResearch.WordTrace tailWord_404275 prefixEnd_404275 207587391596511005903279 := by
  unfold tailWord_404275
  simp only [CollatzResearch.WordTrace]
  refine ⟨14745120610388194518182279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9830080406925463012121519 14745120610388194518182279)
  ·
    refine ⟨22117680915582291777273419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14745120610388194518182279 22117680915582291777273419)
    ·
      refine ⟨33176521373373437665910129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22117680915582291777273419 33176521373373437665910129)
      ·
        refine ⟨24882391030030078249432597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33176521373373437665910129 24882391030030078249432597)
        ·
          refine ⟨1166362079532659917942153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24882391030030078249432597 1166362079532659917942153)
          ·
            refine ⟨874771559649494938456615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166362079532659917942153 874771559649494938456615)
            ·
              refine ⟨1312157339474242407684923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 874771559649494938456615 1312157339474242407684923)
              ·
                refine ⟨1968236009211363611527385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1312157339474242407684923 1968236009211363611527385)
                ·
                  refine ⟨1476177006908522708645539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1968236009211363611527385 1476177006908522708645539)
                  ·
                    refine ⟨2214265510362784062968309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1476177006908522708645539 2214265510362784062968309)
                    ·
                      refine ⟨207587391596511005903279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2214265510362784062968309 207587391596511005903279)
                      ·
                        rfl

theorem cell23_404275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_404275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404275 prefixEnd_404275 := by exact prefixLift 404275
  have htrace : WordTrace (prefixWord ++ tailWord_404275) baseStart_404275 baseEnd_404275 := by
    simpa [prefixWord, tailWord_404275, baseEnd_404275] using wordTrace_append hprefix tailTrace_404275
  have hstable : (prefixWord ++ tailWord_404275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404275).length < 2 ^ (prefixWord ++ tailWord_404275).sum := by decide
  have hdescent : baseEnd_404275 < baseStart_404275 := by decide
  rcases family_descends (prefixWord ++ tailWord_404275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404298 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_404298 : Nat := 118140960795 + 404298 * 2 ^ 59
def prefixEnd_404298 : Nat := 4983230072969 + 3 ^ 40 * 404298 * 2
def baseEnd_404298 : Nat := 207599201651564415915673

theorem tailTrace_404298 : CollatzResearch.WordTrace tailWord_404298 prefixEnd_404298 207599201651564415915673 := by
  unfold tailWord_404298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686489872326217361567387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9830639659536579630846365 3686489872326217361567387)
  ·
    refine ⟨5529734808489326042351081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686489872326217361567387 5529734808489326042351081)
    ·
      refine ⟨4147301106366994531763311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5529734808489326042351081 4147301106366994531763311)
      ·
        refine ⟨6220951659550491797644967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4147301106366994531763311 6220951659550491797644967)
        ·
          refine ⟨9331427489325737696467451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6220951659550491797644967 9331427489325737696467451)
          ·
            refine ⟨13997141233988606544701177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9331427489325737696467451 13997141233988606544701177)
            ·
              refine ⟨10497855925491454908525883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13997141233988606544701177 10497855925491454908525883)
              ·
                refine ⟨15746783888237182362788825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10497855925491454908525883 15746783888237182362788825)
                ·
                  refine ⟨11810087916177886772091619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15746783888237182362788825 11810087916177886772091619)
                  ·
                    refine ⟨17715131874266830158137429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11810087916177886772091619 17715131874266830158137429)
                    ·
                      refine ⟨207599201651564415915673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17715131874266830158137429 207599201651564415915673)
                      ·
                        rfl

theorem cell23_404298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_404298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404298 prefixEnd_404298 := by exact prefixLift 404298
  have htrace : WordTrace (prefixWord ++ tailWord_404298) baseStart_404298 baseEnd_404298 := by
    simpa [prefixWord, tailWord_404298, baseEnd_404298] using wordTrace_append hprefix tailTrace_404298
  have hstable : (prefixWord ++ tailWord_404298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404298).length < 2 ^ (prefixWord ++ tailWord_404298).sum := by decide
  have hdescent : baseEnd_404298 < baseStart_404298 := by decide
  rcases family_descends (prefixWord ++ tailWord_404298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404325 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_404325 : Nat := 118140960795 + 404325 * 2 ^ 59
def prefixEnd_404325 : Nat := 4983230072969 + 3 ^ 40 * 404325 * 2
def baseEnd_404325 : Nat := 69204355209745270092683

theorem tailTrace_404325 : CollatzResearch.WordTrace tailWord_404325 prefixEnd_404325 69204355209745270092683 := by
  unfold tailWord_404325
  simp only [CollatzResearch.WordTrace]
  refine ⟨14746944260207053057502429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9831296173471368705001619 14746944260207053057502429)
  ·
    refine ⟨5530104097577644896563411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14746944260207053057502429 5530104097577644896563411)
    ·
      refine ⟨8295156146366467344845117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5530104097577644896563411 8295156146366467344845117)
      ·
        refine ⟨3110683554887425254316919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8295156146366467344845117 3110683554887425254316919)
        ·
          refine ⟨4666025332331137881475379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3110683554887425254316919 4666025332331137881475379)
          ·
            refine ⟨6999037998496706822213069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4666025332331137881475379 6999037998496706822213069)
            ·
              refine ⟨2624639249436265058329901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6999037998496706822213069 2624639249436265058329901)
              ·
                refine ⟨984239718538599396873713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2624639249436265058329901 984239718538599396873713)
                ·
                  refine ⟨738179788903949547655285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 984239718538599396873713 738179788903949547655285)
                  ·
                    refine ⟨69204355209745270092683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 738179788903949547655285 69204355209745270092683)
                    ·
                      rfl

theorem cell23_404325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_404325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404325 prefixEnd_404325 := by exact prefixLift 404325
  have htrace : WordTrace (prefixWord ++ tailWord_404325) baseStart_404325 baseEnd_404325 := by
    simpa [prefixWord, tailWord_404325, baseEnd_404325] using wordTrace_append hprefix tailTrace_404325
  have hstable : (prefixWord ++ tailWord_404325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404325).length < 2 ^ (prefixWord ++ tailWord_404325).sum := by decide
  have hdescent : baseEnd_404325 < baseStart_404325 := by decide
  rcases family_descends (prefixWord ++ tailWord_404325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404405 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_404405 : Nat := 118140960795 + 404405 * 2 ^ 59
def prefixEnd_404405 : Nat := 4983230072969 + 3 ^ 40 * 404405 * 2
def baseEnd_404405 : Nat := 207654144081595497277681

theorem tailTrace_404405 : CollatzResearch.WordTrace tailWord_404405 prefixEnd_404405 207654144081595497277681 := by
  unfold tailWord_404405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14749862099917226720414669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9833241399944817813609779 14749862099917226720414669)
  ·
    refine ⟨5531198287468960020155501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14749862099917226720414669 5531198287468960020155501)
    ·
      refine ⟨2074199357800860007558313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5531198287468960020155501 2074199357800860007558313)
      ·
        refine ⟨1555649518350645005668735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074199357800860007558313 1555649518350645005668735)
        ·
          refine ⟨2333474277525967508503103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555649518350645005668735 2333474277525967508503103)
          ·
            refine ⟨3500211416288951262754655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2333474277525967508503103 3500211416288951262754655)
            ·
              refine ⟨5250317124433426894131983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3500211416288951262754655 5250317124433426894131983)
              ·
                refine ⟨7875475686650140341197975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5250317124433426894131983 7875475686650140341197975)
                ·
                  refine ⟨11813213529975210511796963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7875475686650140341197975 11813213529975210511796963)
                  ·
                    refine ⟨17719820294962815767695445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11813213529975210511796963 17719820294962815767695445)
                    ·
                      refine ⟨207654144081595497277681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17719820294962815767695445 207654144081595497277681)
                      ·
                        rfl

theorem cell23_404405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_404405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404405 prefixEnd_404405 := by exact prefixLift 404405
  have htrace : WordTrace (prefixWord ++ tailWord_404405) baseStart_404405 baseEnd_404405 := by
    simpa [prefixWord, tailWord_404405, baseEnd_404405] using wordTrace_append hprefix tailTrace_404405
  have hstable : (prefixWord ++ tailWord_404405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404405).length < 2 ^ (prefixWord ++ tailWord_404405).sum := by decide
  have hdescent : baseEnd_404405 < baseStart_404405 := by decide
  rcases family_descends (prefixWord ++ tailWord_404405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404415 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 3, 5]
def baseStart_404415 : Nat := 118140960795 + 404415 * 2 ^ 59
def prefixEnd_404415 : Nat := 4983230072969 + 3 ^ 40 * 404415 * 2
def baseEnd_404415 : Nat := 69219759629380152717545

theorem tailTrace_404415 : CollatzResearch.WordTrace tailWord_404415 prefixEnd_404415 69219759629380152717545 := by
  unfold tailWord_404415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14750226829880998428278699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9833484553253998952185799 14750226829880998428278699)
  ·
    refine ⟨22125340244821497642418049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14750226829880998428278699 22125340244821497642418049)
    ·
      refine ⟨16594005183616123231813537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22125340244821497642418049 16594005183616123231813537)
      ·
        refine ⟨12445503887712092423860153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16594005183616123231813537 12445503887712092423860153)
        ·
          refine ⟨9334127915784069317895115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12445503887712092423860153 9334127915784069317895115)
          ·
            refine ⟨14001191873676103976842673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9334127915784069317895115 14001191873676103976842673)
            ·
              refine ⟨10500893905257077982632005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14001191873676103976842673 10500893905257077982632005)
              ·
                refine ⟨1968917607235702121743501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10500893905257077982632005 1968917607235702121743501)
                ·
                  refine ⟨738344102713388295653813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1968917607235702121743501 738344102713388295653813)
                  ·
                    refine ⟨69219759629380152717545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 738344102713388295653813 69219759629380152717545)
                    ·
                      rfl

theorem cell23_404415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_404415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404415 prefixEnd_404415 := by exact prefixLift 404415
  have htrace : WordTrace (prefixWord ++ tailWord_404415) baseStart_404415 baseEnd_404415 := by
    simpa [prefixWord, tailWord_404415, baseEnd_404415] using wordTrace_append hprefix tailTrace_404415
  have hstable : (prefixWord ++ tailWord_404415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404415).length < 2 ^ (prefixWord ++ tailWord_404415).sum := by decide
  have hdescent : baseEnd_404415 < baseStart_404415 := by decide
  rcases family_descends (prefixWord ++ tailWord_404415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404463 : List Nat := [1, 1, 2, 1, 4, 4, 3, 2, 1, 1, 3]
def baseStart_404463 : Nat := 118140960795 + 404463 * 2 ^ 59
def prefixEnd_404463 : Nat := 4983230072969 + 3 ^ 40 * 404463 * 2
def baseEnd_404463 : Nat := 207683925959556270352415

theorem tailTrace_404463 : CollatzResearch.WordTrace tailWord_404463 prefixEnd_404463 207683925959556270352415 := by
  unfold tailWord_404463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751977533707102626026043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9834651689138068417350695 14751977533707102626026043)
  ·
    refine ⟨22127966300560653939039065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14751977533707102626026043 22127966300560653939039065)
    ·
      refine ⟨16595974725420490454279299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22127966300560653939039065 16595974725420490454279299)
      ·
        refine ⟨24893962088130735681418949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16595974725420490454279299 24893962088130735681418949)
        ·
          refine ⟨4667617891524512940266053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24893962088130735681418949 4667617891524512940266053)
          ·
            refine ⟨875178354660846176299885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4667617891524512940266053 875178354660846176299885)
            ·
              refine ⟨328191882997817316112457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 875178354660846176299885 328191882997817316112457)
              ·
                refine ⟨246143912248362987084343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328191882997817316112457 246143912248362987084343)
                ·
                  refine ⟨369215868372544480626515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246143912248362987084343 369215868372544480626515)
                  ·
                    refine ⟨553823802558816720939773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369215868372544480626515 553823802558816720939773)
                    ·
                      refine ⟨207683925959556270352415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 553823802558816720939773 207683925959556270352415)
                      ·
                        rfl

theorem cell23_404463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 2, 1, 1, 3].length) (baseStart_404463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404463 prefixEnd_404463 := by exact prefixLift 404463
  have htrace : WordTrace (prefixWord ++ tailWord_404463) baseStart_404463 baseEnd_404463 := by
    simpa [prefixWord, tailWord_404463, baseEnd_404463] using wordTrace_append hprefix tailTrace_404463
  have hstable : (prefixWord ++ tailWord_404463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404463).length < 2 ^ (prefixWord ++ tailWord_404463).sum := by decide
  have hdescent : baseEnd_404463 < baseStart_404463 := by decide
  rcases family_descends (prefixWord ++ tailWord_404463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404472 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_404472 : Nat := 118140960795 + 404472 * 2 ^ 59
def prefixEnd_404472 : Nat := 4983230072969 + 3 ^ 40 * 404472 * 2
def baseEnd_404472 : Nat := 207688547285446735139873

theorem tailTrace_404472 : CollatzResearch.WordTrace tailWord_404472 prefixEnd_404472 207688547285446735139873 := by
  unfold tailWord_404472
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376152895337248581551835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9834870527116331442069113 7376152895337248581551835)
  ·
    refine ⟨11064229343005872872327753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7376152895337248581551835 11064229343005872872327753)
    ·
      refine ⟨8298172007254404654245815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11064229343005872872327753 8298172007254404654245815)
      ·
        refine ⟨12447258010881606981368723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8298172007254404654245815 12447258010881606981368723)
        ·
          refine ⟨18670887016322410472053085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12447258010881606981368723 18670887016322410472053085)
          ·
            refine ⟨7001582631120903927019907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18670887016322410472053085 7001582631120903927019907)
            ·
              refine ⟨10502373946681355890529861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7001582631120903927019907 10502373946681355890529861)
              ·
                refine ⟨1969195115002754229474349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10502373946681355890529861 1969195115002754229474349)
                ·
                  refine ⟨738448168126032836052881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1969195115002754229474349 738448168126032836052881)
                  ·
                    refine ⟨553836126094524627039661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738448168126032836052881 553836126094524627039661)
                    ·
                      refine ⟨207688547285446735139873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 553836126094524627039661 207688547285446735139873)
                      ·
                        rfl

theorem cell23_404472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_404472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404472 prefixEnd_404472 := by exact prefixLift 404472
  have htrace : WordTrace (prefixWord ++ tailWord_404472) baseStart_404472 baseEnd_404472 := by
    simpa [prefixWord, tailWord_404472, baseEnd_404472] using wordTrace_append hprefix tailTrace_404472
  have hstable : (prefixWord ++ tailWord_404472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404472).length < 2 ^ (prefixWord ++ tailWord_404472).sum := by decide
  have hdescent : baseEnd_404472 < baseStart_404472 := by decide
  rcases family_descends (prefixWord ++ tailWord_404472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404506 : List Nat := [3, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3]
def baseStart_404506 : Nat := 118140960795 + 404506 * 2 ^ 59
def prefixEnd_404506 : Nat := 4983230072969 + 3 ^ 40 * 404506 * 2
def baseEnd_404506 : Nat := 207706005627699602114717

theorem tailTrace_404506 : CollatzResearch.WordTrace tailWord_404506 prefixEnd_404506 207706005627699602114717 := by
  unfold tailWord_404506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3688386468137830242460343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9835697248367547313227581 3688386468137830242460343)
  ·
    refine ⟨5532579702206745363690515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3688386468137830242460343 5532579702206745363690515)
    ·
      refine ⟨8298869553310118045535773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5532579702206745363690515 8298869553310118045535773)
      ·
        refine ⟨3112076082491294267075915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8298869553310118045535773 3112076082491294267075915)
        ·
          refine ⟨4668114123736941400613873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112076082491294267075915 4668114123736941400613873)
          ·
            refine ⟨3501085592802706050460405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668114123736941400613873 3501085592802706050460405)
            ·
              refine ⟨328226774325253692230663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3501085592802706050460405 328226774325253692230663)
              ·
                refine ⟨492340161487880538345995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328226774325253692230663 492340161487880538345995)
                ·
                  refine ⟨738510242231820807518993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492340161487880538345995 738510242231820807518993)
                  ·
                    refine ⟨553882681673865605639245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 738510242231820807518993 553882681673865605639245)
                    ·
                      refine ⟨207706005627699602114717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 553882681673865605639245 207706005627699602114717)
                      ·
                        rfl

theorem cell23_404506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_404506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404506 prefixEnd_404506 := by exact prefixLift 404506
  have htrace : WordTrace (prefixWord ++ tailWord_404506) baseStart_404506 baseEnd_404506 := by
    simpa [prefixWord, tailWord_404506, baseEnd_404506] using wordTrace_append hprefix tailTrace_404506
  have hstable : (prefixWord ++ tailWord_404506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404506).length < 2 ^ (prefixWord ++ tailWord_404506).sum := by decide
  have hdescent : baseEnd_404506 < baseStart_404506 := by decide
  rcases family_descends (prefixWord ++ tailWord_404506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404529 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_404529 : Nat := 118140960795 + 404529 * 2 ^ 59
def prefixEnd_404529 : Nat := 4983230072969 + 3 ^ 40 * 404529 * 2
def baseEnd_404529 : Nat := 207717815682753012127111

theorem tailTrace_404529 : CollatzResearch.WordTrace tailWord_404529 prefixEnd_404529 207717815682753012127111 := by
  unfold tailWord_404529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14754384751467995897928641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9836256500978663931952427 14754384751467995897928641)
  ·
    refine ⟨11065788563600996923446481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14754384751467995897928641 11065788563600996923446481)
    ·
      refine ⟨8299341422700747692584861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11065788563600996923446481 8299341422700747692584861)
      ·
        refine ⟨3112253033512780384719323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8299341422700747692584861 3112253033512780384719323)
        ·
          refine ⟨4668379550269170577078985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3112253033512780384719323 4668379550269170577078985)
          ·
            refine ⟨3501284662701877932809239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668379550269170577078985 3501284662701877932809239)
            ·
              refine ⟨5251926994052816899213859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3501284662701877932809239 5251926994052816899213859)
              ·
                refine ⟨7877890491079225348820789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5251926994052816899213859 7877890491079225348820789)
                ·
                  refine ⟨738552233538677376451949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7877890491079225348820789 738552233538677376451949)
                  ·
                    refine ⟨276957087577004016169481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 738552233538677376451949 276957087577004016169481)
                    ·
                      refine ⟨207717815682753012127111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276957087577004016169481 207717815682753012127111)
                      ·
                        rfl

theorem cell23_404529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_404529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404529 prefixEnd_404529 := by exact prefixLift 404529
  have htrace : WordTrace (prefixWord ++ tailWord_404529) baseStart_404529 baseEnd_404529 := by
    simpa [prefixWord, tailWord_404529, baseEnd_404529] using wordTrace_append hprefix tailTrace_404529
  have hstable : (prefixWord ++ tailWord_404529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404529).length < 2 ^ (prefixWord ++ tailWord_404529).sum := by decide
  have hdescent : baseEnd_404529 < baseStart_404529 := by decide
  rcases family_descends (prefixWord ++ tailWord_404529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404536 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_404536 : Nat := 118140960795 + 404536 * 2 ^ 59
def prefixEnd_404536 : Nat := 4983230072969 + 3 ^ 40 * 404536 * 2
def baseEnd_404536 : Nat := 207721410047334484739579

theorem tailTrace_404536 : CollatzResearch.WordTrace tailWord_404536 prefixEnd_404536 207721410047334484739579 := by
  unfold tailWord_404536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7377320031221318046716731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9836426708295090728955641 7377320031221318046716731)
  ·
    refine ⟨11065980046831977070075097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7377320031221318046716731 11065980046831977070075097)
    ·
      refine ⟨8299485035123982802556323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11065980046831977070075097 8299485035123982802556323)
      ·
        refine ⟨12449227552685974203834485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8299485035123982802556323 12449227552685974203834485)
        ·
          refine ⟨1167115083064310081609483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12449227552685974203834485 1167115083064310081609483)
          ·
            refine ⟨1750672624596465122414225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167115083064310081609483 1750672624596465122414225)
            ·
              refine ⟨1313004468447348841810669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750672624596465122414225 1313004468447348841810669)
              ·
                refine ⟨492376675667755815679001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1313004468447348841810669 492376675667755815679001)
                ·
                  refine ⟨369282506750816861759251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492376675667755815679001 369282506750816861759251)
                  ·
                    refine ⟨553923760126225292638877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369282506750816861759251 553923760126225292638877)
                    ·
                      refine ⟨207721410047334484739579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 553923760126225292638877 207721410047334484739579)
                      ·
                        rfl

theorem cell23_404536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_404536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404536 prefixEnd_404536 := by exact prefixLift 404536
  have htrace : WordTrace (prefixWord ++ tailWord_404536) baseStart_404536 baseEnd_404536 := by
    simpa [prefixWord, tailWord_404536, baseEnd_404536] using wordTrace_append hprefix tailTrace_404536
  have hstable : (prefixWord ++ tailWord_404536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404536).length < 2 ^ (prefixWord ++ tailWord_404536).sum := by decide
  have hdescent : baseEnd_404536 < baseStart_404536 := by decide
  rcases family_descends (prefixWord ++ tailWord_404536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404576 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2]
def baseStart_404576 : Nat := 118140960795 + 404576 * 2 ^ 59
def prefixEnd_404576 : Nat := 4983230072969 + 3 ^ 40 * 404576 * 2
def baseEnd_404576 : Nat := 207741949273514328239395

theorem tailTrace_404576 : CollatzResearch.WordTrace tailWord_404576 prefixEnd_404576 207741949273514328239395 := by
  unfold tailWord_404576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7378049491148861462444791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9837399321531815283259721 7378049491148861462444791)
  ·
    refine ⟨11067074236723292193667187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7378049491148861462444791 11067074236723292193667187)
    ·
      refine ⟨16600611355084938290500781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11067074236723292193667187 16600611355084938290500781)
      ·
        refine ⟨6225229258156851858937793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16600611355084938290500781 6225229258156851858937793)
        ·
          refine ⟨4668921943617638894203345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6225229258156851858937793 4668921943617638894203345)
          ·
            refine ⟨3501691457713229170652509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4668921943617638894203345 3501691457713229170652509)
            ·
              refine ⟨1313134296642460938994691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3501691457713229170652509 1313134296642460938994691)
              ·
                refine ⟨1969701444963691408492037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313134296642460938994691 1969701444963691408492037)
                ·
                  refine ⟨369319020930692139092257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1969701444963691408492037 369319020930692139092257)
                  ·
                    refine ⟨276989265698019104319193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369319020930692139092257 276989265698019104319193)
                    ·
                      refine ⟨207741949273514328239395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 276989265698019104319193 207741949273514328239395)
                      ·
                        rfl

theorem cell23_404576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_404576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404576 prefixEnd_404576 := by exact prefixLift 404576
  have htrace : WordTrace (prefixWord ++ tailWord_404576) baseStart_404576 baseEnd_404576 := by
    simpa [prefixWord, tailWord_404576, baseEnd_404576] using wordTrace_append hprefix tailTrace_404576
  have hstable : (prefixWord ++ tailWord_404576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404576).length < 2 ^ (prefixWord ++ tailWord_404576).sum := by decide
  have hdescent : baseEnd_404576 < baseStart_404576 := by decide
  rcases family_descends (prefixWord ++ tailWord_404576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404589 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_404589 : Nat := 118140960795 + 404589 * 2 ^ 59
def prefixEnd_404589 : Nat := 4983230072969 + 3 ^ 40 * 404589 * 2
def baseEnd_404589 : Nat := 207748624522022777376835

theorem tailTrace_404589 : CollatzResearch.WordTrace tailWord_404589 prefixEnd_404589 207748624522022777376835 := by
  unfold tailWord_404589
  simp only [CollatzResearch.WordTrace]
  refine ⟨14756573131250626145112821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9837715420833750763408547 14756573131250626145112821)
  ·
    refine ⟨1383428731054746201104327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14756573131250626145112821 1383428731054746201104327)
    ·
      refine ⟨2075143096582119301656491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1383428731054746201104327 2075143096582119301656491)
      ·
        refine ⟨3112714644873178952484737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2075143096582119301656491 3112714644873178952484737)
        ·
          refine ⟨2334535983654884214363553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3112714644873178952484737 2334535983654884214363553)
          ·
            refine ⟨1750901987741163160772665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334535983654884214363553 1750901987741163160772665)
            ·
              refine ⟨1313176490805872370579499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1750901987741163160772665 1313176490805872370579499)
              ·
                refine ⟨1969764736208808555869249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1313176490805872370579499 1969764736208808555869249)
                ·
                  refine ⟨1477323552156606416901937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1969764736208808555869249 1477323552156606416901937)
                  ·
                    refine ⟨1107992664117454812676453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1477323552156606416901937 1107992664117454812676453)
                    ·
                      refine ⟨207748624522022777376835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1107992664117454812676453 207748624522022777376835)
                      ·
                        rfl

theorem cell23_404589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_404589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404589 prefixEnd_404589 := by exact prefixLift 404589
  have htrace : WordTrace (prefixWord ++ tailWord_404589) baseStart_404589 baseEnd_404589 := by
    simpa [prefixWord, tailWord_404589, baseEnd_404589] using wordTrace_append hprefix tailTrace_404589
  have hstable : (prefixWord ++ tailWord_404589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404589).length < 2 ^ (prefixWord ++ tailWord_404589).sum := by decide
  have hdescent : baseEnd_404589 < baseStart_404589 := by decide
  rcases family_descends (prefixWord ++ tailWord_404589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404659 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 3, 4]
def baseStart_404659 : Nat := 118140960795 + 404659 * 2 ^ 59
def prefixEnd_404659 : Nat := 4983230072969 + 3 ^ 40 * 404659 * 2
def baseEnd_404659 : Nat := 69261522722612501167171

theorem tailTrace_404659 : CollatzResearch.WordTrace tailWord_404659 prefixEnd_404659 69261522722612501167171 := by
  unfold tailWord_404659
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759126240997028100161031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9839417493998018733440687 14759126240997028100161031)
  ·
    refine ⟨22138689361495542150241547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14759126240997028100161031 22138689361495542150241547)
    ·
      refine ⟨33208034042243313225362321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22138689361495542150241547 33208034042243313225362321)
      ·
        refine ⟨24906025531682484919021741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33208034042243313225362321 24906025531682484919021741)
        ·
          refine ⟨9339759574380931844633153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24906025531682484919021741 9339759574380931844633153)
          ·
            refine ⟨7004819680785698883474865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9339759574380931844633153 7004819680785698883474865)
            ·
              refine ⟨5253614760589274162606149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004819680785698883474865 5253614760589274162606149)
              ·
                refine ⟨985052767610488905488653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5253614760589274162606149 985052767610488905488653)
                ·
                  refine ⟨369394787853933339558245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 985052767610488905488653 369394787853933339558245)
                  ·
                    refine ⟨69261522722612501167171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369394787853933339558245 69261522722612501167171)
                    ·
                      rfl

theorem cell23_404659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 3, 4].length) (baseStart_404659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404659 prefixEnd_404659 := by exact prefixLift 404659
  have htrace : WordTrace (prefixWord ++ tailWord_404659) baseStart_404659 baseEnd_404659 := by
    simpa [prefixWord, tailWord_404659, baseEnd_404659] using wordTrace_append hprefix tailTrace_404659
  have hstable : (prefixWord ++ tailWord_404659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404659).length < 2 ^ (prefixWord ++ tailWord_404659).sum := by decide
  have hdescent : baseEnd_404659 < baseStart_404659 := by decide
  rcases family_descends (prefixWord ++ tailWord_404659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404669 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_404669 : Nat := 118140960795 + 404669 * 2 ^ 59
def prefixEnd_404669 : Nat := 4983230072969 + 3 ^ 40 * 404669 * 2
def baseEnd_404669 : Nat := 207789702974382464376467

theorem tailTrace_404669 : CollatzResearch.WordTrace tailWord_404669 prefixEnd_404669 207789702974382464376467 := by
  unfold tailWord_404669
  simp only [CollatzResearch.WordTrace]
  refine ⟨14759490970960799808025061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9839660647307199872016707 14759490970960799808025061)
  ·
    refine ⟨2767404557055149964004699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14759490970960799808025061 2767404557055149964004699)
    ·
      refine ⟨4151106835582724946007049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2767404557055149964004699 4151106835582724946007049)
      ·
        refine ⟨3113330126687043709505287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4151106835582724946007049 3113330126687043709505287)
        ·
          refine ⟨4669995190030565564257931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113330126687043709505287 4669995190030565564257931)
          ·
            refine ⟨7004992785045848346386897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4669995190030565564257931 7004992785045848346386897)
            ·
              refine ⟨5253744588784386259790173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7004992785045848346386897 5253744588784386259790173)
              ·
                refine ⟨1970154220794144847421315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5253744588784386259790173 1970154220794144847421315)
                ·
                  refine ⟨2955231331191217271131973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1970154220794144847421315 2955231331191217271131973)
                  ·
                    refine ⟨554105874598353238337245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2955231331191217271131973 554105874598353238337245)
                    ·
                      refine ⟨207789702974382464376467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 554105874598353238337245 207789702974382464376467)
                      ·
                        rfl

theorem cell23_404669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_404669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404669 prefixEnd_404669 := by exact prefixLift 404669
  have htrace : WordTrace (prefixWord ++ tailWord_404669) baseStart_404669 baseEnd_404669 := by
    simpa [prefixWord, tailWord_404669, baseEnd_404669] using wordTrace_append hprefix tailTrace_404669
  have hstable : (prefixWord ++ tailWord_404669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404669).length < 2 ^ (prefixWord ++ tailWord_404669).sum := by decide
  have hdescent : baseEnd_404669 < baseStart_404669 := by decide
  rcases family_descends (prefixWord ++ tailWord_404669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404716 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 3]
def baseStart_404716 : Nat := 118140960795 + 404716 * 2 ^ 59
def prefixEnd_404716 : Nat := 4983230072969 + 3 ^ 40 * 404716 * 2
def baseEnd_404716 : Nat := 207813836565143780488751

theorem tailTrace_404716 : CollatzResearch.WordTrace tailWord_404716 prefixEnd_404716 207813836565143780488751 := by
  unfold tailWord_404716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7380602600895263417493001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9840803467860351223324001 7380602600895263417493001)
  ·
    refine ⟨5535451950671447563119751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7380602600895263417493001 5535451950671447563119751)
    ·
      refine ⟨8303177926007171344679627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5535451950671447563119751 8303177926007171344679627)
      ·
        refine ⟨12454766889010757017019441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8303177926007171344679627 12454766889010757017019441)
        ·
          refine ⟨9341075166758067762764581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12454766889010757017019441 9341075166758067762764581)
          ·
            refine ⟨1751451593767137705518359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9341075166758067762764581 1751451593767137705518359)
            ·
              refine ⟨2627177390650706558277539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1751451593767137705518359 2627177390650706558277539)
              ·
                refine ⟨3940766085976059837416309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627177390650706558277539 3940766085976059837416309)
                ·
                  refine ⟨369446820560255609757779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3940766085976059837416309 369446820560255609757779)
                  ·
                    refine ⟨554170230840383414636669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369446820560255609757779 554170230840383414636669)
                    ·
                      refine ⟨207813836565143780488751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 554170230840383414636669 207813836565143780488751)
                      ·
                        rfl

theorem cell23_404716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 3].length) (baseStart_404716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404716 prefixEnd_404716 := by exact prefixLift 404716
  have htrace : WordTrace (prefixWord ++ tailWord_404716) baseStart_404716 baseEnd_404716 := by
    simpa [prefixWord, tailWord_404716, baseEnd_404716] using wordTrace_append hprefix tailTrace_404716
  have hstable : (prefixWord ++ tailWord_404716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404716).length < 2 ^ (prefixWord ++ tailWord_404716).sum := by decide
  have hdescent : baseEnd_404716 < baseStart_404716 := by decide
  rcases family_descends (prefixWord ++ tailWord_404716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404750 : List Nat := [4, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3]
def baseStart_404750 : Nat := 118140960795 + 404750 * 2 ^ 59
def prefixEnd_404750 : Nat := 4983230072969 + 3 ^ 40 * 404750 * 2
def baseEnd_404750 : Nat := 207831294907396647463595

theorem tailTrace_404750 : CollatzResearch.WordTrace tailWord_404750 prefixEnd_404750 207831294907396647463595 := by
  unfold tailWord_404750
  simp only [CollatzResearch.WordTrace]
  refine ⟨1845305660458418830215463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9841630189111567094482469 1845305660458418830215463)
  ·
    refine ⟨2767958490687628245323195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1845305660458418830215463 2767958490687628245323195)
    ·
      refine ⟨4151937736031442367984793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2767958490687628245323195 4151937736031442367984793)
      ·
        refine ⟨3113953302023581775988595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4151937736031442367984793 3113953302023581775988595)
        ·
          refine ⟨4670929953035372663982893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3113953302023581775988595 4670929953035372663982893)
          ·
            refine ⟨1751598732388264748993585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4670929953035372663982893 1751598732388264748993585)
            ·
              refine ⟨1313699049291198561745189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1751598732388264748993585 1313699049291198561745189)
              ·
                refine ⟨246318571742099730327223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1313699049291198561745189 246318571742099730327223)
                ·
                  refine ⟨369477857613149595490835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246318571742099730327223 369477857613149595490835)
                  ·
                    refine ⟨554216786419724393236253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 369477857613149595490835 554216786419724393236253)
                    ·
                      refine ⟨207831294907396647463595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 554216786419724393236253 207831294907396647463595)
                      ·
                        rfl

theorem cell23_404750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 4, 1, 1, 3].length) (baseStart_404750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404750 prefixEnd_404750 := by exact prefixLift 404750
  have htrace : WordTrace (prefixWord ++ tailWord_404750) baseStart_404750 baseEnd_404750 := by
    simpa [prefixWord, tailWord_404750, baseEnd_404750] using wordTrace_append hprefix tailTrace_404750
  have hstable : (prefixWord ++ tailWord_404750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404750).length < 2 ^ (prefixWord ++ tailWord_404750).sum := by decide
  have hdescent : baseEnd_404750 < baseStart_404750 := by decide
  rcases family_descends (prefixWord ++ tailWord_404750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404773 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_404773 : Nat := 118140960795 + 404773 * 2 ^ 59
def prefixEnd_404773 : Nat := 4983230072969 + 3 ^ 40 * 404773 * 2
def baseEnd_404773 : Nat := 207843104962450057475989

theorem tailTrace_404773 : CollatzResearch.WordTrace tailWord_404773 prefixEnd_404773 207843104962450057475989 := by
  unfold tailWord_404773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14763284162584025569810973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9842189441722683713207315 14763284162584025569810973)
  ·
    refine ⟨5536231560969009588679115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14763284162584025569810973 5536231560969009588679115)
    ·
      refine ⟨8304347341453514383018673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5536231560969009588679115 8304347341453514383018673)
      ·
        refine ⟨6228260506090135787264005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8304347341453514383018673 6228260506090135787264005)
        ·
          refine ⟨1167798844891900460112001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6228260506090135787264005 1167798844891900460112001)
          ·
            refine ⟨875849133668925345084001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167798844891900460112001 875849133668925345084001)
            ·
              refine ⟨656886850251694008813001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875849133668925345084001 656886850251694008813001)
              ·
                refine ⟨492665137688770506609751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 656886850251694008813001 492665137688770506609751)
                ·
                  refine ⟨738997706533155759914627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492665137688770506609751 738997706533155759914627)
                  ·
                    refine ⟨1108496559799733639871941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 738997706533155759914627 1108496559799733639871941)
                    ·
                      refine ⟨207843104962450057475989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1108496559799733639871941 207843104962450057475989)
                      ·
                        rfl

theorem cell23_404773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_404773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404773 prefixEnd_404773 := by exact prefixLift 404773
  have htrace : WordTrace (prefixWord ++ tailWord_404773) baseStart_404773 baseEnd_404773 := by
    simpa [prefixWord, tailWord_404773, baseEnd_404773] using wordTrace_append hprefix tailTrace_404773
  have hstable : (prefixWord ++ tailWord_404773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404773).length < 2 ^ (prefixWord ++ tailWord_404773).sum := by decide
  have hdescent : baseEnd_404773 < baseStart_404773 := by decide
  rcases family_descends (prefixWord ++ tailWord_404773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404793 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 5]
def baseStart_404793 : Nat := 118140960795 + 404793 * 2 ^ 59
def prefixEnd_404793 : Nat := 4983230072969 + 3 ^ 40 * 404793 * 2
def baseEnd_404793 : Nat := 207853374575539979225897

theorem tailTrace_404793 : CollatzResearch.WordTrace tailWord_404793 prefixEnd_404793 207853374575539979225897 := by
  unfold tailWord_404793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764013622511568985539033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9842675748341045990359355 14764013622511568985539033)
  ·
    refine ⟨11073010216883676739154275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14764013622511568985539033 11073010216883676739154275)
    ·
      refine ⟨16609515325325515108731413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11073010216883676739154275 16609515325325515108731413)
      ·
        refine ⟨778571030874633520721785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16609515325325515108731413 778571030874633520721785)
        ·
          refine ⟨583928273155975140541339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 778571030874633520721785 583928273155975140541339)
          ·
            refine ⟨875892409733962710812009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583928273155975140541339 875892409733962710812009)
            ·
              refine ⟨656919307300472033109007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875892409733962710812009 656919307300472033109007)
              ·
                refine ⟨985378960950708049663511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656919307300472033109007 985378960950708049663511)
                ·
                  refine ⟨1478068441426062074495267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 985378960950708049663511 1478068441426062074495267)
                  ·
                    refine ⟨2217102662139093111742901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1478068441426062074495267 2217102662139093111742901)
                    ·
                      refine ⟨207853374575539979225897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2217102662139093111742901 207853374575539979225897)
                      ·
                        rfl

theorem cell23_404793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_404793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404793 prefixEnd_404793 := by exact prefixLift 404793
  have htrace : WordTrace (prefixWord ++ tailWord_404793) baseStart_404793 baseEnd_404793 := by
    simpa [prefixWord, tailWord_404793, baseEnd_404793] using wordTrace_append hprefix tailTrace_404793
  have hstable : (prefixWord ++ tailWord_404793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404793).length < 2 ^ (prefixWord ++ tailWord_404793).sum := by decide
  have hdescent : baseEnd_404793 < baseStart_404793 := by decide
  rcases family_descends (prefixWord ++ tailWord_404793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404876 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_404876 : Nat := 118140960795 + 404876 * 2 ^ 59
def prefixEnd_404876 : Nat := 4983230072969 + 3 ^ 40 * 404876 * 2
def baseEnd_404876 : Nat := 207895993469863154488015

theorem tailTrace_404876 : CollatzResearch.WordTrace tailWord_404876 prefixEnd_404876 207895993469863154488015 := by
  unfold tailWord_404876
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383520440605437080405241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9844693920807249440540321 7383520440605437080405241)
  ·
    refine ⟨5537640330454077810303931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7383520440605437080405241 5537640330454077810303931)
    ·
      refine ⟨8306460495681116715455897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5537640330454077810303931 8306460495681116715455897)
      ·
        refine ⟨6229845371760837536591923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8306460495681116715455897 6229845371760837536591923)
        ·
          refine ⟨9344768057641256304887885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6229845371760837536591923 9344768057641256304887885)
          ·
            refine ⟨3504288021615471114332957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9344768057641256304887885 3504288021615471114332957)
            ·
              refine ⟨1314108008105801667874859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3504288021615471114332957 1314108008105801667874859)
              ·
                refine ⟨1971162012158702501812289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314108008105801667874859 1971162012158702501812289)
                ·
                  refine ⟨1478371509119026876359217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1971162012158702501812289 1478371509119026876359217)
                  ·
                    refine ⟨1108778631839270157269413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1478371509119026876359217 1108778631839270157269413)
                    ·
                      refine ⟨207895993469863154488015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1108778631839270157269413 207895993469863154488015)
                      ·
                        rfl

theorem cell23_404876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_404876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404876 prefixEnd_404876 := by exact prefixLift 404876
  have htrace : WordTrace (prefixWord ++ tailWord_404876) baseStart_404876 baseEnd_404876 := by
    simpa [prefixWord, tailWord_404876, baseEnd_404876] using wordTrace_append hprefix tailTrace_404876
  have hstable : (prefixWord ++ tailWord_404876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404876).length < 2 ^ (prefixWord ++ tailWord_404876).sum := by decide
  have hdescent : baseEnd_404876 < baseStart_404876 := by decide
  rcases family_descends (prefixWord ++ tailWord_404876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404896 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3]
def baseStart_404896 : Nat := 118140960795 + 404896 * 2 ^ 59
def prefixEnd_404896 : Nat := 4983230072969 + 3 ^ 40 * 404896 * 2
def baseEnd_404896 : Nat := 207906263082953076237923

theorem tailTrace_404896 : CollatzResearch.WordTrace tailWord_404896 prefixEnd_404896 207906263082953076237923 := by
  unfold tailWord_404896
  simp only [CollatzResearch.WordTrace]
  refine ⟨7383885170569208788269271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9845180227425611717692361 7383885170569208788269271)
  ·
    refine ⟨11075827755853813182403907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7383885170569208788269271 11075827755853813182403907)
    ·
      refine ⟨16613741633780719773605861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11075827755853813182403907 16613741633780719773605861)
      ·
        refine ⟨3115076556333884957551099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16613741633780719773605861 3115076556333884957551099)
        ·
          refine ⟨4672614834500827436326649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115076556333884957551099 4672614834500827436326649)
          ·
            refine ⟨3504461125875620577244987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4672614834500827436326649 3504461125875620577244987)
            ·
              refine ⟨5256691688813430865867481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504461125875620577244987 5256691688813430865867481)
              ·
                refine ⟨3942518766610073149400611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5256691688813430865867481 3942518766610073149400611)
                ·
                  refine ⟨5913778149915109724100917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942518766610073149400611 5913778149915109724100917)
                  ·
                    refine ⟨554416701554541536634461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5913778149915109724100917 554416701554541536634461)
                    ·
                      refine ⟨207906263082953076237923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 554416701554541536634461 207906263082953076237923)
                      ·
                        rfl

theorem cell23_404896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_404896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404896 prefixEnd_404896 := by exact prefixLift 404896
  have htrace : WordTrace (prefixWord ++ tailWord_404896) baseStart_404896 baseEnd_404896 := by
    simpa [prefixWord, tailWord_404896, baseEnd_404896] using wordTrace_append hprefix tailTrace_404896
  have hstable : (prefixWord ++ tailWord_404896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404896).length < 2 ^ (prefixWord ++ tailWord_404896).sum := by decide
  have hdescent : baseEnd_404896 < baseStart_404896 := by decide
  rcases family_descends (prefixWord ++ tailWord_404896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404926 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_404926 : Nat := 118140960795 + 404926 * 2 ^ 59
def prefixEnd_404926 : Nat := 4983230072969 + 3 ^ 40 * 404926 * 2
def baseEnd_404926 : Nat := 207921667502587958862785

theorem tailTrace_404926 : CollatzResearch.WordTrace tailWord_404926 prefixEnd_404926 207921667502587958862785 := by
  unfold tailWord_404926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1846108066378716587516329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9845909687353155133420421 1846108066378716587516329)
  ·
    refine ⟨1384581049784037440637247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1846108066378716587516329 1384581049784037440637247)
    ·
      refine ⟨2076871574676056160955871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1384581049784037440637247 2076871574676056160955871)
      ·
        refine ⟨3115307362014084241433807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2076871574676056160955871 3115307362014084241433807)
        ·
          refine ⟨4672961043021126362150711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3115307362014084241433807 4672961043021126362150711)
          ·
            refine ⟨7009441564531689543226067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4672961043021126362150711 7009441564531689543226067)
            ·
              refine ⟨10514162346797534314839101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7009441564531689543226067 10514162346797534314839101)
              ·
                refine ⟨3942810880049075368064663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10514162346797534314839101 3942810880049075368064663)
                ·
                  refine ⟨5914216320073613052096995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3942810880049075368064663 5914216320073613052096995)
                  ·
                    refine ⟨8871324480110419578145493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5914216320073613052096995 8871324480110419578145493)
                    ·
                      refine ⟨207921667502587958862785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8871324480110419578145493 207921667502587958862785)
                      ·
                        rfl

theorem cell23_404926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_404926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404926 prefixEnd_404926 := by exact prefixLift 404926
  have htrace : WordTrace (prefixWord ++ tailWord_404926) baseStart_404926 baseEnd_404926 := by
    simpa [prefixWord, tailWord_404926, baseEnd_404926] using wordTrace_append hprefix tailTrace_404926
  have hstable : (prefixWord ++ tailWord_404926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404926).length < 2 ^ (prefixWord ++ tailWord_404926).sum := by decide
  have hdescent : baseEnd_404926 < baseStart_404926 := by decide
  rcases family_descends (prefixWord ++ tailWord_404926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404936 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_404936 : Nat := 118140960795 + 404936 * 2 ^ 59
def prefixEnd_404936 : Nat := 4983230072969 + 3 ^ 40 * 404936 * 2
def baseEnd_404936 : Nat := 207926802309132919737739

theorem tailTrace_404936 : CollatzResearch.WordTrace tailWord_404936 prefixEnd_404936 207926802309132919737739 := by
  unfold tailWord_404936
  simp only [CollatzResearch.WordTrace]
  refine ⟨7384614630496752203997331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9846152840662336271996441 7384614630496752203997331)
  ·
    refine ⟨11076921945745128305995997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7384614630496752203997331 11076921945745128305995997)
    ·
      refine ⟨4153845729654423114748499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11076921945745128305995997 4153845729654423114748499)
      ·
        refine ⟨6230768594481634672122749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4153845729654423114748499 6230768594481634672122749)
        ·
          refine ⟨2336538222930613002046031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6230768594481634672122749 2336538222930613002046031)
          ·
            refine ⟨3504807334395919503069047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336538222930613002046031 3504807334395919503069047)
            ·
              refine ⟨5257211001593879254603571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3504807334395919503069047 5257211001593879254603571)
              ·
                refine ⟨7885816502390818881905357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5257211001593879254603571 7885816502390818881905357)
                ·
                  refine ⟨2957181188396557080714509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7885816502390818881905357 2957181188396557080714509)
                  ·
                    refine ⟨1108942945648708905267941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2957181188396557080714509 1108942945648708905267941)
                    ·
                      refine ⟨207926802309132919737739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1108942945648708905267941 207926802309132919737739)
                      ·
                        rfl

theorem cell23_404936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_404936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404936 prefixEnd_404936 := by exact prefixLift 404936
  have htrace : WordTrace (prefixWord ++ tailWord_404936) baseStart_404936 baseEnd_404936 := by
    simpa [prefixWord, tailWord_404936, baseEnd_404936] using wordTrace_append hprefix tailTrace_404936
  have hstable : (prefixWord ++ tailWord_404936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404936).length < 2 ^ (prefixWord ++ tailWord_404936).sum := by decide
  have hdescent : baseEnd_404936 < baseStart_404936 := by decide
  rcases family_descends (prefixWord ++ tailWord_404936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404970 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_404970 : Nat := 118140960795 + 404970 * 2 ^ 59
def prefixEnd_404970 : Nat := 4983230072969 + 3 ^ 40 * 404970 * 2
def baseEnd_404970 : Nat := 207944260651385786712583

theorem tailTrace_404970 : CollatzResearch.WordTrace tailWord_404970 prefixEnd_404970 207944260651385786712583 := by
  unfold tailWord_404970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692617335717582053683091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9846979561913552143154909 3692617335717582053683091)
  ·
    refine ⟨5538926003576373080524637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3692617335717582053683091 5538926003576373080524637)
    ·
      refine ⟨2077097251341139905196739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5538926003576373080524637 2077097251341139905196739)
      ·
        refine ⟨3115645877011709857795109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2077097251341139905196739 3115645877011709857795109)
        ·
          refine ⟨584183601939695598336583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3115645877011709857795109 584183601939695598336583)
          ·
            refine ⟨876275402909543397504875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584183601939695598336583 876275402909543397504875)
            ·
              refine ⟨1314413104364315096257313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876275402909543397504875 1314413104364315096257313)
              ·
                refine ⟨985809828273236322192985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1314413104364315096257313 985809828273236322192985)
                ·
                  refine ⟨739357371204927241644739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 985809828273236322192985 739357371204927241644739)
                  ·
                    refine ⟨1109036056807390862467109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 739357371204927241644739 1109036056807390862467109)
                    ·
                      refine ⟨207944260651385786712583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1109036056807390862467109 207944260651385786712583)
                      ·
                        rfl

theorem cell23_404970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_404970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404970 prefixEnd_404970 := by exact prefixLift 404970
  have htrace : WordTrace (prefixWord ++ tailWord_404970) baseStart_404970 baseEnd_404970 := by
    simpa [prefixWord, tailWord_404970, baseEnd_404970] using wordTrace_append hprefix tailTrace_404970
  have hstable : (prefixWord ++ tailWord_404970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404970).length < 2 ^ (prefixWord ++ tailWord_404970).sum := by decide
  have hdescent : baseEnd_404970 < baseStart_404970 := by decide
  rcases family_descends (prefixWord ++ tailWord_404970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404976 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 8]
def baseStart_404976 : Nat := 118140960795 + 404976 * 2 ^ 59
def prefixEnd_404976 : Nat := 4983230072969 + 3 ^ 40 * 404976 * 2
def baseEnd_404976 : Nat := 23105260170590307026395

theorem tailTrace_404976 : CollatzResearch.WordTrace tailWord_404976 prefixEnd_404976 23105260170590307026395 := by
  unfold tailWord_404976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7385344090424295619725391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9847125453899060826300521 7385344090424295619725391)
  ·
    refine ⟨11078016135636443429588087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7385344090424295619725391 11078016135636443429588087)
    ·
      refine ⟨16617024203454665144382131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11078016135636443429588087 16617024203454665144382131)
      ·
        refine ⟨24925536305181997716573197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16617024203454665144382131 24925536305181997716573197)
        ·
          refine ⟨9347076114443249143714949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24925536305181997716573197 9347076114443249143714949)
          ·
            refine ⟨1752576771458109214446553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9347076114443249143714949 1752576771458109214446553)
            ·
              refine ⟨1314432578593581910834915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1752576771458109214446553 1314432578593581910834915)
              ·
                refine ⟨1971648867890372866252373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1314432578593581910834915 1971648867890372866252373)
                ·
                  refine ⟨23105260170590307026395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1971648867890372866252373 23105260170590307026395)
                  ·
                    rfl

theorem cell23_404976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 8].length) (baseStart_404976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_404976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_404976 prefixEnd_404976 := by exact prefixLift 404976
  have htrace : WordTrace (prefixWord ++ tailWord_404976) baseStart_404976 baseEnd_404976 := by
    simpa [prefixWord, tailWord_404976, baseEnd_404976] using wordTrace_append hprefix tailTrace_404976
  have hstable : (prefixWord ++ tailWord_404976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404976).length < 2 ^ (prefixWord ++ tailWord_404976).sum := by decide
  have hdescent : baseEnd_404976 < baseStart_404976 := by decide
  rcases family_descends (prefixWord ++ tailWord_404976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405023 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 1, 5]
def baseStart_405023 : Nat := 118140960795 + 405023 * 2 ^ 59
def prefixEnd_405023 : Nat := 4983230072969 + 3 ^ 40 * 405023 * 2
def baseEnd_405023 : Nat := 69323825042024693116613

theorem tailTrace_405023 : CollatzResearch.WordTrace tailWord_405023 prefixEnd_405023 69323825042024693116613 := by
  unfold tailWord_405023
  simp only [CollatzResearch.WordTrace]
  refine ⟨14772402411678318266411723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9848268274452212177607815 14772402411678318266411723)
  ·
    refine ⟨22158603617517477399617585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14772402411678318266411723 22158603617517477399617585)
    ·
      refine ⟨16618952713138108049713189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22158603617517477399617585 16618952713138108049713189)
      ·
        refine ⟨3116053633713395259321223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16618952713138108049713189 3116053633713395259321223)
        ·
          refine ⟨4674080450570092888981835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3116053633713395259321223 4674080450570092888981835)
          ·
            refine ⟨7011120675855139333472753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4674080450570092888981835 7011120675855139333472753)
            ·
              refine ⟨5258340506891354500104565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7011120675855139333472753 5258340506891354500104565)
              ·
                refine ⟨492969422521064484384803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5258340506891354500104565 492969422521064484384803)
                ·
                  refine ⟨739454133781596726577205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 492969422521064484384803 739454133781596726577205)
                  ·
                    refine ⟨69323825042024693116613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 739454133781596726577205 69323825042024693116613)
                    ·
                      rfl

theorem cell23_405023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 1, 5].length) (baseStart_405023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405023 prefixEnd_405023 := by exact prefixLift 405023
  have htrace : WordTrace (prefixWord ++ tailWord_405023) baseStart_405023 baseEnd_405023 := by
    simpa [prefixWord, tailWord_405023, baseEnd_405023] using wordTrace_append hprefix tailTrace_405023
  have hstable : (prefixWord ++ tailWord_405023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405023).length < 2 ^ (prefixWord ++ tailWord_405023).sum := by decide
  have hdescent : baseEnd_405023 < baseStart_405023 := by decide
  rcases family_descends (prefixWord ++ tailWord_405023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405043 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4]
def baseStart_405043 : Nat := 118140960795 + 405043 * 2 ^ 59
def prefixEnd_405043 : Nat := 4983230072969 + 3 ^ 40 * 405043 * 2
def baseEnd_405043 : Nat := 207981744739164001099747

theorem tailTrace_405043 : CollatzResearch.WordTrace tailWord_405043 prefixEnd_405043 207981744739164001099747 := by
  unfold tailWord_405043
  simp only [CollatzResearch.WordTrace]
  refine ⟨14773131871605861682139783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9848754581070574454759855 14773131871605861682139783)
  ·
    refine ⟨22159697807408792523209675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14773131871605861682139783 22159697807408792523209675)
    ·
      refine ⟨33239546711113188784814513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22159697807408792523209675 33239546711113188784814513)
      ·
        refine ⟨24929660033334891588610885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33239546711113188784814513 24929660033334891588610885)
        ·
          refine ⟨4674311256250292172864541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24929660033334891588610885 4674311256250292172864541)
          ·
            refine ⟨1752866721093859564824203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4674311256250292172864541 1752866721093859564824203)
            ·
              refine ⟨2629300081640789347236305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752866721093859564824203 2629300081640789347236305)
              ·
                refine ⟨1971975061230592010427229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2629300081640789347236305 1971975061230592010427229)
                ·
                  refine ⟨739490647961472003910211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1971975061230592010427229 739490647961472003910211)
                  ·
                    refine ⟨1109235971942208005865317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 739490647961472003910211 1109235971942208005865317)
                    ·
                      refine ⟨207981744739164001099747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1109235971942208005865317 207981744739164001099747)
                      ·
                        rfl

theorem cell23_405043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 3, 1, 4].length) (baseStart_405043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405043 prefixEnd_405043 := by exact prefixLift 405043
  have htrace : WordTrace (prefixWord ++ tailWord_405043) baseStart_405043 baseEnd_405043 := by
    simpa [prefixWord, tailWord_405043, baseEnd_405043] using wordTrace_append hprefix tailTrace_405043
  have hstable : (prefixWord ++ tailWord_405043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405043).length < 2 ^ (prefixWord ++ tailWord_405043).sum := by decide
  have hdescent : baseEnd_405043 < baseStart_405043 := by decide
  rcases family_descends (prefixWord ++ tailWord_405043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405073 : List Nat := [1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_405073 : Nat := 118140960795 + 405073 * 2 ^ 59
def prefixEnd_405073 : Nat := 4983230072969 + 3 ^ 40 * 405073 * 2
def baseEnd_405073 : Nat := 207997149158798883724609

theorem tailTrace_405073 : CollatzResearch.WordTrace tailWord_405073 prefixEnd_405073 207997149158798883724609 := by
  unfold tailWord_405073
  simp only [CollatzResearch.WordTrace]
  refine ⟨14774226061497176805731873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9849484040998117870487915 14774226061497176805731873)
  ·
    refine ⟨11080669546122882604298905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14774226061497176805731873 11080669546122882604298905)
    ·
      refine ⟨8310502159592161953224179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11080669546122882604298905 8310502159592161953224179)
      ·
        refine ⟨12465753239388242929836269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8310502159592161953224179 12465753239388242929836269)
        ·
          refine ⟨4674657464770591098688601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12465753239388242929836269 4674657464770591098688601)
          ·
            refine ⟨3505993098577943324016451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4674657464770591098688601 3505993098577943324016451)
            ·
              refine ⟨5258989647866914986024677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3505993098577943324016451 5258989647866914986024677)
              ·
                refine ⟨986060558975046559879627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5258989647866914986024677 986060558975046559879627)
                ·
                  refine ⟨1479090838462569839819441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986060558975046559879627 1479090838462569839819441)
                  ·
                    refine ⟨1109318128846927379864581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1479090838462569839819441 1109318128846927379864581)
                    ·
                      refine ⟨207997149158798883724609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1109318128846927379864581 207997149158798883724609)
                      ·
                        rfl

theorem cell23_405073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_405073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405073 prefixEnd_405073 := by exact prefixLift 405073
  have htrace : WordTrace (prefixWord ++ tailWord_405073) baseStart_405073 baseEnd_405073 := by
    simpa [prefixWord, tailWord_405073, baseEnd_405073] using wordTrace_append hprefix tailTrace_405073
  have hstable : (prefixWord ++ tailWord_405073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405073).length < 2 ^ (prefixWord ++ tailWord_405073).sum := by decide
  have hdescent : baseEnd_405073 < baseStart_405073 := by decide
  rcases family_descends (prefixWord ++ tailWord_405073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405203 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 8, 5]
def baseStart_405203 : Nat := 118140960795 + 405203 * 2 ^ 59
def prefixEnd_405203 : Nat := 4983230072969 + 3 ^ 40 * 405203 * 2
def baseEnd_405203 : Nat := 69354633881294458366337

theorem tailTrace_405203 : CollatzResearch.WordTrace tailWord_405203 prefixEnd_405203 69354633881294458366337 := by
  unfold tailWord_405203
  simp only [CollatzResearch.WordTrace]
  refine ⟨14778967551026209007964263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9852645034017472671976175 14778967551026209007964263)
  ·
    refine ⟨22168451326539313511946395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14778967551026209007964263 22168451326539313511946395)
    ·
      refine ⟨33252676989808970267919593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22168451326539313511946395 33252676989808970267919593)
      ·
        refine ⟨24939507742356727700939695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33252676989808970267919593 24939507742356727700939695)
        ·
          refine ⟨37409261613535091551409543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24939507742356727700939695 37409261613535091551409543)
          ·
            refine ⟨56113892420302637327114315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37409261613535091551409543 56113892420302637327114315)
            ·
              refine ⟨84170838630453955990671473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56113892420302637327114315 84170838630453955990671473)
              ·
                refine ⟨63128128972840466993003605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84170838630453955990671473 63128128972840466993003605)
                ·
                  refine ⟨739782761400474222574261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 63128128972840466993003605 739782761400474222574261)
                  ·
                    refine ⟨69354633881294458366337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 739782761400474222574261 69354633881294458366337)
                    ·
                      rfl

theorem cell23_405203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 8, 5].length) (baseStart_405203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405203 prefixEnd_405203 := by exact prefixLift 405203
  have htrace : WordTrace (prefixWord ++ tailWord_405203) baseStart_405203 baseEnd_405203 := by
    simpa [prefixWord, tailWord_405203, baseEnd_405203] using wordTrace_append hprefix tailTrace_405203
  have hstable : (prefixWord ++ tailWord_405203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405203).length < 2 ^ (prefixWord ++ tailWord_405203).sum := by decide
  have hdescent : baseEnd_405203 < baseStart_405203 := by decide
  rcases family_descends (prefixWord ++ tailWord_405203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405217 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_405217 : Nat := 118140960795 + 405217 * 2 ^ 59
def prefixEnd_405217 : Nat := 4983230072969 + 3 ^ 40 * 405217 * 2
def baseEnd_405217 : Nat := 208071090373046320323947

theorem tailTrace_405217 : CollatzResearch.WordTrace tailWord_405217 prefixEnd_405217 208071090373046320323947 := by
  unfold tailWord_405217
  simp only [CollatzResearch.WordTrace]
  refine ⟨14779478172975489398973905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9852985448650326265982603 14779478172975489398973905)
  ·
    refine ⟨11084608629731617049230429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14779478172975489398973905 11084608629731617049230429)
    ·
      refine ⟨4156728236149356393461411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11084608629731617049230429 4156728236149356393461411)
      ·
        refine ⟨6235092354224034590192117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4156728236149356393461411 6235092354224034590192117)
        ·
          refine ⟨584539908208503242830511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6235092354224034590192117 584539908208503242830511)
          ·
            refine ⟨876809862312754864245767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584539908208503242830511 876809862312754864245767)
            ·
              refine ⟨1315214793469132296368651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876809862312754864245767 1315214793469132296368651)
              ·
                refine ⟨1972822190203698444552977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315214793469132296368651 1972822190203698444552977)
                ·
                  refine ⟨1479616642652773833414733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1972822190203698444552977 1479616642652773833414733)
                  ·
                    refine ⟨554856240994790187530525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1479616642652773833414733 554856240994790187530525)
                    ·
                      refine ⟨208071090373046320323947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 554856240994790187530525 208071090373046320323947)
                      ·
                        rfl

theorem cell23_405217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_405217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405217 prefixEnd_405217 := by exact prefixLift 405217
  have htrace : WordTrace (prefixWord ++ tailWord_405217) baseStart_405217 baseEnd_405217 := by
    simpa [prefixWord, tailWord_405217, baseEnd_405217] using wordTrace_append hprefix tailTrace_405217
  have hstable : (prefixWord ++ tailWord_405217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405217).length < 2 ^ (prefixWord ++ tailWord_405217).sum := by decide
  have hdescent : baseEnd_405217 < baseStart_405217 := by decide
  rcases family_descends (prefixWord ++ tailWord_405217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405240 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_405240 : Nat := 118140960795 + 405240 * 2 ^ 59
def prefixEnd_405240 : Nat := 4983230072969 + 3 ^ 40 * 405240 * 2
def baseEnd_405240 : Nat := 208082900428099730336341

theorem tailTrace_405240 : CollatzResearch.WordTrace tailWord_405240 prefixEnd_405240 208082900428099730336341 := by
  unfold tailWord_405240
  simp only [CollatzResearch.WordTrace]
  refine ⟨7390158525946082163530587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9853544701261442884707449 7390158525946082163530587)
  ·
    refine ⟨11085237788919123245295881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7390158525946082163530587 11085237788919123245295881)
    ·
      refine ⟨8313928341689342433971911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11085237788919123245295881 8313928341689342433971911)
      ·
        refine ⟨12470892512534013650957867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8313928341689342433971911 12470892512534013650957867)
        ·
          refine ⟨18706338768801020476436801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12470892512534013650957867 18706338768801020476436801)
          ·
            refine ⟨14029754076600765357327601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18706338768801020476436801 14029754076600765357327601)
            ·
              refine ⟨10522315557450574017995701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14029754076600765357327601 10522315557450574017995701)
              ·
                refine ⟨986467083510991314187097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10522315557450574017995701 986467083510991314187097)
                ·
                  refine ⟨739850312633243485640323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 986467083510991314187097 739850312633243485640323)
                  ·
                    refine ⟨1109775468949865228460485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 739850312633243485640323 1109775468949865228460485)
                    ·
                      refine ⟨208082900428099730336341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1109775468949865228460485 208082900428099730336341)
                      ·
                        rfl

theorem cell23_405240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_405240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405240 prefixEnd_405240 := by exact prefixLift 405240
  have htrace : WordTrace (prefixWord ++ tailWord_405240) baseStart_405240 baseEnd_405240 := by
    simpa [prefixWord, tailWord_405240, baseEnd_405240] using wordTrace_append hprefix tailTrace_405240
  have hstable : (prefixWord ++ tailWord_405240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405240).length < 2 ^ (prefixWord ++ tailWord_405240).sum := by decide
  have hdescent : baseEnd_405240 < baseStart_405240 := by decide
  rcases family_descends (prefixWord ++ tailWord_405240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405243 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5]
def baseStart_405243 : Nat := 118140960795 + 405243 * 2 ^ 59
def prefixEnd_405243 : Nat := 4983230072969 + 3 ^ 40 * 405243 * 2
def baseEnd_405243 : Nat := 208084440870063218598827

theorem tailTrace_405243 : CollatzResearch.WordTrace tailWord_405243 prefixEnd_405243 208084440870063218598827 := by
  unfold tailWord_405243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14780426470881295839420383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9853617647254197226280255 14780426470881295839420383)
  ·
    refine ⟨22170639706321943759130575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14780426470881295839420383 22170639706321943759130575)
    ·
      refine ⟨33255959559482915638695863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22170639706321943759130575 33255959559482915638695863)
      ·
        refine ⟨49883939339224373458043795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33255959559482915638695863 49883939339224373458043795)
        ·
          refine ⟨74825909008836560187065693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49883939339224373458043795 74825909008836560187065693)
          ·
            refine ⟨28059715878313710070149635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74825909008836560187065693 28059715878313710070149635)
            ·
              refine ⟨42089573817470565105224453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28059715878313710070149635 42089573817470565105224453)
              ·
                refine ⟨7891795090775730957229585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42089573817470565105224453 7891795090775730957229585)
                ·
                  refine ⟨5918846318081798217922189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7891795090775730957229585 5918846318081798217922189)
                  ·
                    refine ⟨2219567369280674331720821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5918846318081798217922189 2219567369280674331720821)
                    ·
                      refine ⟨208084440870063218598827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2219567369280674331720821 208084440870063218598827)
                      ·
                        rfl

theorem cell23_405243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 5].length) (baseStart_405243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405243 prefixEnd_405243 := by exact prefixLift 405243
  have htrace : WordTrace (prefixWord ++ tailWord_405243) baseStart_405243 baseEnd_405243 := by
    simpa [prefixWord, tailWord_405243, baseEnd_405243] using wordTrace_append hprefix tailTrace_405243
  have hstable : (prefixWord ++ tailWord_405243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405243).length < 2 ^ (prefixWord ++ tailWord_405243).sum := by decide
  have hdescent : baseEnd_405243 < baseStart_405243 := by decide
  rcases family_descends (prefixWord ++ tailWord_405243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405273 : List Nat := [1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 9]
def baseStart_405273 : Nat := 118140960795 + 405273 * 2 ^ 59
def prefixEnd_405273 : Nat := 4983230072969 + 3 ^ 40 * 405273 * 2
def baseEnd_405273 : Nat := 208099845289698101223689

theorem tailTrace_405273 : CollatzResearch.WordTrace tailWord_405273 prefixEnd_405273 208099845289698101223689 := by
  unfold tailWord_405273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14781520660772610963012473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9854347107181740642008315 14781520660772610963012473)
  ·
    refine ⟨11086140495579458222259355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14781520660772610963012473 11086140495579458222259355)
    ·
      refine ⟨16629210743369187333389033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11086140495579458222259355 16629210743369187333389033)
      ·
        refine ⟨12471908057526890500041775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16629210743369187333389033 12471908057526890500041775)
        ·
          refine ⟨18707862086290335750062663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12471908057526890500041775 18707862086290335750062663)
          ·
            refine ⟨28061793129435503625093995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18707862086290335750062663 28061793129435503625093995)
            ·
              refine ⟨42092689694153255437640993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28061793129435503625093995 42092689694153255437640993)
              ·
                refine ⟨31569517270614941578230745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42092689694153255437640993 31569517270614941578230745)
                ·
                  refine ⟨23677137952961206183673059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31569517270614941578230745 23677137952961206183673059)
                  ·
                    refine ⟨35515706929441809275509589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23677137952961206183673059 35515706929441809275509589)
                    ·
                      refine ⟨208099845289698101223689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 35515706929441809275509589 208099845289698101223689)
                      ·
                        rfl

theorem cell23_405273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_405273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405273 prefixEnd_405273 := by exact prefixLift 405273
  have htrace : WordTrace (prefixWord ++ tailWord_405273) baseStart_405273 baseEnd_405273 := by
    simpa [prefixWord, tailWord_405273, baseEnd_405273] using wordTrace_append hprefix tailTrace_405273
  have hstable : (prefixWord ++ tailWord_405273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405273).length < 2 ^ (prefixWord ++ tailWord_405273).sum := by decide
  have hdescent : baseEnd_405273 < baseStart_405273 := by decide
  rcases family_descends (prefixWord ++ tailWord_405273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405318 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 3, 4]
def baseStart_405318 : Nat := 118140960795 + 405318 * 2 ^ 59
def prefixEnd_405318 : Nat := 4983230072969 + 3 ^ 40 * 405318 * 2
def baseEnd_405318 : Nat := 69374317306383475053661

theorem tailTrace_405318 : CollatzResearch.WordTrace tailWord_405318 prefixEnd_405318 69374317306383475053661 := by
  unfold tailWord_405318
  simp only [CollatzResearch.WordTrace]
  refine ⟨461973810800299489012519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9855441297073055765600405 461973810800299489012519)
  ·
    refine ⟨692960716200449233518779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 461973810800299489012519 692960716200449233518779)
    ·
      refine ⟨1039441074300673850278169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692960716200449233518779 1039441074300673850278169)
      ·
        refine ⟨779580805725505387708627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1039441074300673850278169 779580805725505387708627)
        ·
          refine ⟨1169371208588258081562941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779580805725505387708627 1169371208588258081562941)
          ·
            refine ⟨438514203220596780586103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169371208588258081562941 438514203220596780586103)
            ·
              refine ⟨657771304830895170879155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438514203220596780586103 657771304830895170879155)
              ·
                refine ⟨986656957246342756318733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657771304830895170879155 986656957246342756318733)
                ·
                  refine ⟨369996358967378533619525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 986656957246342756318733 369996358967378533619525)
                  ·
                    refine ⟨69374317306383475053661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 369996358967378533619525 69374317306383475053661)
                    ·
                      rfl

theorem cell23_405318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_405318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405318 prefixEnd_405318 := by exact prefixLift 405318
  have htrace : WordTrace (prefixWord ++ tailWord_405318) baseStart_405318 baseEnd_405318 := by
    simpa [prefixWord, tailWord_405318, baseEnd_405318] using wordTrace_append hprefix tailTrace_405318
  have hstable : (prefixWord ++ tailWord_405318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405318).length < 2 ^ (prefixWord ++ tailWord_405318).sum := by decide
  have hdescent : baseEnd_405318 < baseStart_405318 := by decide
  rcases family_descends (prefixWord ++ tailWord_405318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405344 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_405344 : Nat := 118140960795 + 405344 * 2 ^ 59
def prefixEnd_405344 : Nat := 4983230072969 + 3 ^ 40 * 405344 * 2
def baseEnd_405344 : Nat := 69378767472055774478621

theorem tailTrace_405344 : CollatzResearch.WordTrace tailWord_405344 prefixEnd_405344 69378767472055774478621 := by
  unfold tailWord_405344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7392055121757695044423543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9856073495676926725898057 7392055121757695044423543)
  ·
    refine ⟨11088082682636542566635315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7392055121757695044423543 11088082682636542566635315)
    ·
      refine ⟨16632124023954813849952973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11088082682636542566635315 16632124023954813849952973)
      ·
        refine ⟨6237046508983055193732365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16632124023954813849952973 6237046508983055193732365)
        ·
          refine ⟨2338892440868645697649637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6237046508983055193732365 2338892440868645697649637)
          ·
            refine ⟨438542332662871068309307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2338892440868645697649637 438542332662871068309307)
            ·
              refine ⟨657813498994306602463961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438542332662871068309307 657813498994306602463961)
              ·
                refine ⟨493360124245729951847971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 657813498994306602463961 493360124245729951847971)
                ·
                  refine ⟨740040186368594927771957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493360124245729951847971 740040186368594927771957)
                  ·
                    refine ⟨69378767472055774478621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 740040186368594927771957 69378767472055774478621)
                    ·
                      rfl

theorem cell23_405344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_405344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405344 prefixEnd_405344 := by exact prefixLift 405344
  have htrace : WordTrace (prefixWord ++ tailWord_405344) baseStart_405344 baseEnd_405344 := by
    simpa [prefixWord, tailWord_405344, baseEnd_405344] using wordTrace_append hprefix tailTrace_405344
  have hstable : (prefixWord ++ tailWord_405344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405344).length < 2 ^ (prefixWord ++ tailWord_405344).sum := by decide
  have hdescent : baseEnd_405344 < baseStart_405344 := by decide
  rcases family_descends (prefixWord ++ tailWord_405344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405357 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_405357 : Nat := 118140960795 + 405357 * 2 ^ 59
def prefixEnd_405357 : Nat := 4983230072969 + 3 ^ 40 * 405357 * 2
def baseEnd_405357 : Nat := 69380992554891924191101

theorem tailTrace_405357 : CollatzResearch.WordTrace tailWord_405357 prefixEnd_405357 69380992554891924191101 := by
  unfold tailWord_405357
  simp only [CollatzResearch.WordTrace]
  refine ⟨14784584392468293309070325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9856389594978862206046883 14784584392468293309070325)
  ·
    refine ⟨1386054786793902497725343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14784584392468293309070325 1386054786793902497725343)
    ·
      refine ⟨2079082180190853746588015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386054786793902497725343 2079082180190853746588015)
      ·
        refine ⟨3118623270286280619882023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079082180190853746588015 3118623270286280619882023)
        ·
          refine ⟨4677934905429420929823035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3118623270286280619882023 4677934905429420929823035)
          ·
            refine ⟨7016902358144131394734553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4677934905429420929823035 7016902358144131394734553)
            ·
              refine ⟨5262676768608098546050915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7016902358144131394734553 5262676768608098546050915)
              ·
                refine ⟨7894015152912147819076373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5262676768608098546050915 7894015152912147819076373)
                ·
                  refine ⟨370031960292756929019205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7894015152912147819076373 370031960292756929019205)
                  ·
                    refine ⟨69380992554891924191101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 370031960292756929019205 69380992554891924191101)
                    ·
                      rfl

theorem cell23_405357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_405357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405357 prefixEnd_405357 := by exact prefixLift 405357
  have htrace : WordTrace (prefixWord ++ tailWord_405357) baseStart_405357 baseEnd_405357 := by
    simpa [prefixWord, tailWord_405357, baseEnd_405357] using wordTrace_append hprefix tailTrace_405357
  have hstable : (prefixWord ++ tailWord_405357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405357).length < 2 ^ (prefixWord ++ tailWord_405357).sum := by decide
  have hdescent : baseEnd_405357 < baseStart_405357 := by decide
  rcases family_descends (prefixWord ++ tailWord_405357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405394 : List Nat := [3, 2, 3, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_405394 : Nat := 118140960795 + 405394 * 2 ^ 59
def prefixEnd_405394 : Nat := 4983230072969 + 3 ^ 40 * 405394 * 2
def baseEnd_405394 : Nat := 208161976448892127810633

theorem tailTrace_405394 : CollatzResearch.WordTrace tailWord_405394 prefixEnd_405394 208161976448892127810633 := by
  unfold tailWord_405394
  simp only [CollatzResearch.WordTrace]
  refine ⟨3696483473333562157041809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9857289262222832418778157 3696483473333562157041809)
  ·
    refine ⟨2772362605000171617781357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3696483473333562157041809 2772362605000171617781357)
    ·
      refine ⟨1039635976875064356668009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2772362605000171617781357 1039635976875064356668009)
      ·
        refine ⟨779726982656298267501007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1039635976875064356668009 779726982656298267501007)
        ·
          refine ⟨1169590473984447401251511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779726982656298267501007 1169590473984447401251511)
          ·
            refine ⟨1754385710976671101877267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169590473984447401251511 1754385710976671101877267)
            ·
              refine ⟨2631578566465006652815901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754385710976671101877267 2631578566465006652815901)
              ·
                refine ⟨986841962424377494805963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2631578566465006652815901 986841962424377494805963)
                ·
                  refine ⟨1480262943636566242208945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 986841962424377494805963 1480262943636566242208945)
                  ·
                    refine ⟨1110197207727424681656709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1480262943636566242208945 1110197207727424681656709)
                    ·
                      refine ⟨208161976448892127810633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1110197207727424681656709 208161976448892127810633)
                      ·
                        rfl

theorem cell23_405394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_405394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405394 prefixEnd_405394 := by exact prefixLift 405394
  have htrace : WordTrace (prefixWord ++ tailWord_405394) baseStart_405394 baseEnd_405394 := by
    simpa [prefixWord, tailWord_405394, baseEnd_405394] using wordTrace_append hprefix tailTrace_405394
  have hstable : (prefixWord ++ tailWord_405394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405394).length < 2 ^ (prefixWord ++ tailWord_405394).sum := by decide
  have hdescent : baseEnd_405394 < baseStart_405394 := by decide
  rcases family_descends (prefixWord ++ tailWord_405394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405404 : List Nat := [2, 2, 3, 3, 1, 2, 3, 7]
def baseStart_405404 : Nat := 118140960795 + 405404 * 2 ^ 59
def prefixEnd_405404 : Nat := 4983230072969 + 3 ^ 40 * 405404 * 2
def baseEnd_405404 : Nat := 7709893009460632914281

theorem tailTrace_405404 : CollatzResearch.WordTrace tailWord_405404 prefixEnd_405404 7709893009460632914281 := by
  unfold tailWord_405404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393149311649010168015633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9857532415532013557354177 7393149311649010168015633)
  ·
    refine ⟨5544861983736757626011725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7393149311649010168015633 5544861983736757626011725)
    ·
      refine ⟨2079323243901284109754397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5544861983736757626011725 2079323243901284109754397)
      ·
        refine ⟨779746216462981541157899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2079323243901284109754397 779746216462981541157899)
        ·
          refine ⟨1169619324694472311736849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 779746216462981541157899 1169619324694472311736849)
          ·
            refine ⟨877214493520854233802637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169619324694472311736849 877214493520854233802637)
            ·
              refine ⟨328955435070320337675989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 877214493520854233802637 328955435070320337675989)
              ·
                refine ⟨7709893009460632914281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 328955435070320337675989 7709893009460632914281)
                ·
                  rfl

theorem cell23_405404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 7].length) (baseStart_405404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405404 prefixEnd_405404 := by exact prefixLift 405404
  have htrace : WordTrace (prefixWord ++ tailWord_405404) baseStart_405404 baseEnd_405404 := by
    simpa [prefixWord, tailWord_405404, baseEnd_405404] using wordTrace_append hprefix tailTrace_405404
  have hstable : (prefixWord ++ tailWord_405404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405404).length < 2 ^ (prefixWord ++ tailWord_405404).sum := by decide
  have hdescent : baseEnd_405404 < baseStart_405404 := by decide
  rcases family_descends (prefixWord ++ tailWord_405404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405415 : List Nat := [1, 1, 6, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_405415 : Nat := 118140960795 + 405415 * 2 ^ 59
def prefixEnd_405415 : Nat := 4983230072969 + 3 ^ 40 * 405415 * 2
def baseEnd_405415 : Nat := 208172759542636545648037

theorem tailTrace_405415 : CollatzResearch.WordTrace tailWord_405415 prefixEnd_405415 208172759542636545648037 := by
  unfold tailWord_405415
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786699826258169214681699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9857799884172112809787799 14786699826258169214681699)
  ·
    refine ⟨22180049739387253822022549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14786699826258169214681699 22180049739387253822022549)
    ·
      refine ⟨1039689831533777522907307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22180049739387253822022549 1039689831533777522907307)
      ·
        refine ⟨1559534747300666284360961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1039689831533777522907307 1559534747300666284360961)
        ·
          refine ⟨1169651060475499713270721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559534747300666284360961 1169651060475499713270721)
          ·
            refine ⟨877238295356624784953041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169651060475499713270721 877238295356624784953041)
            ·
              refine ⟨657928721517468588714781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877238295356624784953041 657928721517468588714781)
              ·
                refine ⟨246723270569050720768043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 657928721517468588714781 246723270569050720768043)
                ·
                  refine ⟨370084905853576081152065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 246723270569050720768043 370084905853576081152065)
                  ·
                    refine ⟨277563679390182060864049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 370084905853576081152065 277563679390182060864049)
                    ·
                      refine ⟨208172759542636545648037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 277563679390182060864049 208172759542636545648037)
                      ·
                        rfl

theorem cell23_405415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_405415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405415 prefixEnd_405415 := by exact prefixLift 405415
  have htrace : WordTrace (prefixWord ++ tailWord_405415) baseStart_405415 baseEnd_405415 := by
    simpa [prefixWord, tailWord_405415, baseEnd_405415] using wordTrace_append hprefix tailTrace_405415
  have hstable : (prefixWord ++ tailWord_405415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405415).length < 2 ^ (prefixWord ++ tailWord_405415).sum := by decide
  have hdescent : baseEnd_405415 < baseStart_405415 := by decide
  rcases family_descends (prefixWord ++ tailWord_405415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405448 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_405448 : Nat := 118140960795 + 405448 * 2 ^ 59
def prefixEnd_405448 : Nat := 4983230072969 + 3 ^ 40 * 405448 * 2
def baseEnd_405448 : Nat := 208189704404234916535385

theorem tailTrace_405448 : CollatzResearch.WordTrace tailWord_405448 prefixEnd_405448 208189704404234916535385 := by
  unfold tailWord_405448
  simp only [CollatzResearch.WordTrace]
  refine ⟨7393951717569307925316499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9858602290092410567088665 7393951717569307925316499)
  ·
    refine ⟨11090927576353961887974749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7393951717569307925316499 11090927576353961887974749)
    ·
      refine ⟨4159097841132735707990531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11090927576353961887974749 4159097841132735707990531)
      ·
        refine ⟨6238646761699103561985797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159097841132735707990531 6238646761699103561985797)
        ·
          refine ⟨1169746267818581917872337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6238646761699103561985797 1169746267818581917872337)
          ·
            refine ⟨877309700863936438404253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1169746267818581917872337 877309700863936438404253)
            ·
              refine ⟨328991137823976164401595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 877309700863936438404253 328991137823976164401595)
              ·
                refine ⟨493486706735964246602393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328991137823976164401595 493486706735964246602393)
                ·
                  refine ⟨370115030051973184951795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493486706735964246602393 370115030051973184951795)
                  ·
                    refine ⟨555172545077959777427693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370115030051973184951795 555172545077959777427693)
                    ·
                      refine ⟨208189704404234916535385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 555172545077959777427693 208189704404234916535385)
                      ·
                        rfl

theorem cell23_405448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_405448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405448 prefixEnd_405448 := by exact prefixLift 405448
  have htrace : WordTrace (prefixWord ++ tailWord_405448) baseStart_405448 baseEnd_405448 := by
    simpa [prefixWord, tailWord_405448, baseEnd_405448] using wordTrace_append hprefix tailTrace_405448
  have hstable : (prefixWord ++ tailWord_405448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405448).length < 2 ^ (prefixWord ++ tailWord_405448).sum := by decide
  have hdescent : baseEnd_405448 < baseStart_405448 := by decide
  rcases family_descends (prefixWord ++ tailWord_405448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405471 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 4, 2, 2]
def baseStart_405471 : Nat := 118140960795 + 405471 * 2 ^ 59
def prefixEnd_405471 : Nat := 4983230072969 + 3 ^ 40 * 405471 * 2
def baseEnd_405471 : Nat := 208201514459288326547779

theorem tailTrace_405471 : CollatzResearch.WordTrace tailWord_405471 prefixEnd_405471 208201514459288326547779 := by
  unfold tailWord_405471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14788742314055290778720267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9859161542703527185813511 14788742314055290778720267)
  ·
    refine ⟨22183113471082936168080401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14788742314055290778720267 22183113471082936168080401)
    ·
      refine ⟨16637335103312202126060301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22183113471082936168080401 16637335103312202126060301)
      ·
        refine ⟨6239000663742075797272613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16637335103312202126060301 6239000663742075797272613)
        ·
          refine ⟨1169812624451639211988615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6239000663742075797272613 1169812624451639211988615)
          ·
            refine ⟨1754718936677458817982923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1169812624451639211988615 1754718936677458817982923)
            ·
              refine ⟨2632078405016188226974385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754718936677458817982923 2632078405016188226974385)
              ·
                refine ⟨1974058803762141170230789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632078405016188226974385 1974058803762141170230789)
                ·
                  refine ⟨370136025705401469418273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974058803762141170230789 370136025705401469418273)
                  ·
                    refine ⟨277602019279051102063705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 370136025705401469418273 277602019279051102063705)
                    ·
                      refine ⟨208201514459288326547779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 277602019279051102063705 208201514459288326547779)
                      ·
                        rfl

theorem cell23_405471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_405471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405471 prefixEnd_405471 := by exact prefixLift 405471
  have htrace : WordTrace (prefixWord ++ tailWord_405471) baseStart_405471 baseEnd_405471 := by
    simpa [prefixWord, tailWord_405471, baseEnd_405471] using wordTrace_append hprefix tailTrace_405471
  have hstable : (prefixWord ++ tailWord_405471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405471).length < 2 ^ (prefixWord ++ tailWord_405471).sum := by decide
  have hdescent : baseEnd_405471 < baseStart_405471 := by decide
  rcases family_descends (prefixWord ++ tailWord_405471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405564 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_405564 : Nat := 118140960795 + 405564 * 2 ^ 59
def prefixEnd_405564 : Nat := 4983230072969 + 3 ^ 40 * 405564 * 2
def baseEnd_405564 : Nat := 208249268160156462684851

theorem tailTrace_405564 : CollatzResearch.WordTrace tailWord_405564 prefixEnd_405564 208249268160156462684851 := by
  unfold tailWord_405564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396067151359183830927873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9861422868478911774570497 7396067151359183830927873)
  ·
    refine ⟨5547050363519387873195905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7396067151359183830927873 5547050363519387873195905)
    ·
      refine ⟨4160287772639540904896929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5547050363519387873195905 4160287772639540904896929)
      ·
        refine ⟨3120215829479655678672697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4160287772639540904896929 3120215829479655678672697)
        ·
          refine ⟨2340161872109741759004523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3120215829479655678672697 2340161872109741759004523)
          ·
            refine ⟨3510242808164612638506785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340161872109741759004523 3510242808164612638506785)
            ·
              refine ⟨2632682106123459478880089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3510242808164612638506785 2632682106123459478880089)
              ·
                refine ⟨1974511579592594609160067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2632682106123459478880089 1974511579592594609160067)
                ·
                  refine ⟨2961767369388891913740101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974511579592594609160067 2961767369388891913740101)
                  ·
                    refine ⟨555331381760417233826269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961767369388891913740101 555331381760417233826269)
                    ·
                      refine ⟨208249268160156462684851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 555331381760417233826269 208249268160156462684851)
                      ·
                        rfl

theorem cell23_405564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_405564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405564 prefixEnd_405564 := by exact prefixLift 405564
  have htrace : WordTrace (prefixWord ++ tailWord_405564) baseStart_405564 baseEnd_405564 := by
    simpa [prefixWord, tailWord_405564, baseEnd_405564] using wordTrace_append hprefix tailTrace_405564
  have hstable : (prefixWord ++ tailWord_405564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405564).length < 2 ^ (prefixWord ++ tailWord_405564).sum := by decide
  have hdescent : baseEnd_405564 < baseStart_405564 := by decide
  rcases family_descends (prefixWord ++ tailWord_405564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405581 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_405581 : Nat := 118140960795 + 405581 * 2 ^ 59
def prefixEnd_405581 : Nat := 4983230072969 + 3 ^ 40 * 405581 * 2
def baseEnd_405581 : Nat := 208257997331282896172273

theorem tailTrace_405581 : CollatzResearch.WordTrace tailWord_405581 prefixEnd_405581 208257997331282896172273 := by
  unfold tailWord_405581
  simp only [CollatzResearch.WordTrace]
  refine ⟨14792754343656779565224597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9861836229104519710149731 14792754343656779565224597)
  ·
    refine ⟨693410359858911542119903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14792754343656779565224597 693410359858911542119903)
    ·
      refine ⟨1040115539788367313179855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693410359858911542119903 1040115539788367313179855)
      ·
        refine ⟨1560173309682550969769783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040115539788367313179855 1560173309682550969769783)
        ·
          refine ⟨2340259964523826454654675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560173309682550969769783 2340259964523826454654675)
          ·
            refine ⟨3510389946785739681982013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340259964523826454654675 3510389946785739681982013)
            ·
              refine ⟨1316396230044652380743255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3510389946785739681982013 1316396230044652380743255)
              ·
                refine ⟨1974594345066978571114883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316396230044652380743255 1974594345066978571114883)
                ·
                  refine ⟨2961891517600467856672325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974594345066978571114883 2961891517600467856672325)
                  ·
                    refine ⟨555354659550087723126061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2961891517600467856672325 555354659550087723126061)
                    ·
                      refine ⟨208257997331282896172273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 555354659550087723126061 208257997331282896172273)
                      ·
                        rfl

theorem cell23_405581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_405581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405581 prefixEnd_405581 := by exact prefixLift 405581
  have htrace : WordTrace (prefixWord ++ tailWord_405581) baseStart_405581 baseEnd_405581 := by
    simpa [prefixWord, tailWord_405581, baseEnd_405581] using wordTrace_append hprefix tailTrace_405581
  have hstable : (prefixWord ++ tailWord_405581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405581).length < 2 ^ (prefixWord ++ tailWord_405581).sum := by decide
  have hdescent : baseEnd_405581 < baseStart_405581 := by decide
  rcases family_descends (prefixWord ++ tailWord_405581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405661 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_405661 : Nat := 118140960795 + 405661 * 2 ^ 59
def prefixEnd_405661 : Nat := 4983230072969 + 3 ^ 40 * 405661 * 2
def baseEnd_405661 : Nat := 69433025261214194390635

theorem tailTrace_405661 : CollatzResearch.WordTrace tailWord_405661 prefixEnd_405661 69433025261214194390635 := by
  unfold tailWord_405661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14795672183366953228136837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9863781455577968818757891 14795672183366953228136837)
  ·
    refine ⟨2774188534381303730275657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14795672183366953228136837 2774188534381303730275657)
    ·
      refine ⟨2080641400785977797706743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2774188534381303730275657 2080641400785977797706743)
      ·
        refine ⟨3120962101178966696560115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2080641400785977797706743 3120962101178966696560115)
        ·
          refine ⟨4681443151768450044840173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120962101178966696560115 4681443151768450044840173)
          ·
            refine ⟨1755541181913168766815065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4681443151768450044840173 1755541181913168766815065)
            ·
              refine ⟨1316655886434876575111299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755541181913168766815065 1316655886434876575111299)
              ·
                refine ⟨1974983829652314862666949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1316655886434876575111299 1974983829652314862666949)
                ·
                  refine ⟨370309468059809036750053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1974983829652314862666949 370309468059809036750053)
                  ·
                    refine ⟨69433025261214194390635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 370309468059809036750053 69433025261214194390635)
                    ·
                      rfl

theorem cell23_405661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_405661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405661 prefixEnd_405661 := by exact prefixLift 405661
  have htrace : WordTrace (prefixWord ++ tailWord_405661) baseStart_405661 baseEnd_405661 := by
    simpa [prefixWord, tailWord_405661, baseEnd_405661] using wordTrace_append hprefix tailTrace_405661
  have hstable : (prefixWord ++ tailWord_405661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405661).length < 2 ^ (prefixWord ++ tailWord_405661).sum := by decide
  have hdescent : baseEnd_405661 < baseStart_405661 := by decide
  rcases family_descends (prefixWord ++ tailWord_405661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405662 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_405662 : Nat := 118140960795 + 405662 * 2 ^ 59
def prefixEnd_405662 : Nat := 4983230072969 + 3 ^ 40 * 405662 * 2
def baseEnd_405662 : Nat := 208299589264297079259401

theorem tailTrace_405662 : CollatzResearch.WordTrace tailWord_405662 prefixEnd_405662 208299589264297079259401 := by
  unfold tailWord_405662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1849463582045416299865405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9863805770908886932615493 1849463582045416299865405)
  ·
    refine ⟨693548843267031112449527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1849463582045416299865405 693548843267031112449527)
    ·
      refine ⟨1040323264900546668674291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693548843267031112449527 1040323264900546668674291)
      ·
        refine ⟨1560484897350820003011437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040323264900546668674291 1560484897350820003011437)
        ·
          refine ⟨585181836506557501129289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1560484897350820003011437 585181836506557501129289)
          ·
            refine ⟨438886377379918125846967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585181836506557501129289 438886377379918125846967)
            ·
              refine ⟨658329566069877188770451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438886377379918125846967 658329566069877188770451)
              ·
                refine ⟨987494349104815783155677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 658329566069877188770451 987494349104815783155677)
                ·
                  refine ⟨370310380914305918683379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 987494349104815783155677 370310380914305918683379)
                  ·
                    refine ⟨555465571371458878025069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370310380914305918683379 555465571371458878025069)
                    ·
                      refine ⟨208299589264297079259401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 555465571371458878025069 208299589264297079259401)
                      ·
                        rfl

theorem cell23_405662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_405662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405662 prefixEnd_405662 := by exact prefixLift 405662
  have htrace : WordTrace (prefixWord ++ tailWord_405662) baseStart_405662 baseEnd_405662 := by
    simpa [prefixWord, tailWord_405662, baseEnd_405662] using wordTrace_append hprefix tailTrace_405662
  have hstable : (prefixWord ++ tailWord_405662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405662).length < 2 ^ (prefixWord ++ tailWord_405662).sum := by decide
  have hdescent : baseEnd_405662 < baseStart_405662 := by decide
  rcases family_descends (prefixWord ++ tailWord_405662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405664 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_405664 : Nat := 118140960795 + 405664 * 2 ^ 59
def prefixEnd_405664 : Nat := 4983230072969 + 3 ^ 40 * 405664 * 2
def baseEnd_405664 : Nat := 208300616225606071434391

theorem tailTrace_405664 : CollatzResearch.WordTrace tailWord_405664 prefixEnd_405664 208300616225606071434391 := by
  unfold tailWord_405664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7397890801178042370248023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9863854401570723160330697 7397890801178042370248023)
  ·
    refine ⟨11096836201767063555372035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7397890801178042370248023 11096836201767063555372035)
    ·
      refine ⟨16645254302650595333058053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11096836201767063555372035 16645254302650595333058053)
      ·
        refine ⟨3120985181746986624948385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16645254302650595333058053 3120985181746986624948385)
        ·
          refine ⟨2340738886310239968711289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3120985181746986624948385 2340738886310239968711289)
          ·
            refine ⟨1755554164732679976533467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2340738886310239968711289 1755554164732679976533467)
            ·
              refine ⟨2633331247099019964800201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1755554164732679976533467 2633331247099019964800201)
              ·
                refine ⟨1974998435324264973600151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2633331247099019964800201 1974998435324264973600151)
                ·
                  refine ⟨2962497652986397460400227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1974998435324264973600151 2962497652986397460400227)
                  ·
                    refine ⟨4443746479479596190600341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2962497652986397460400227 4443746479479596190600341)
                    ·
                      refine ⟨208300616225606071434391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4443746479479596190600341 208300616225606071434391)
                      ·
                        rfl

theorem cell23_405664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_405664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405664 prefixEnd_405664 := by exact prefixLift 405664
  have htrace : WordTrace (prefixWord ++ tailWord_405664) baseStart_405664 baseEnd_405664 := by
    simpa [prefixWord, tailWord_405664, baseEnd_405664] using wordTrace_append hprefix tailTrace_405664
  have hstable : (prefixWord ++ tailWord_405664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405664).length < 2 ^ (prefixWord ++ tailWord_405664).sum := by decide
  have hdescent : baseEnd_405664 < baseStart_405664 := by decide
  rcases family_descends (prefixWord ++ tailWord_405664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405701 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_405701 : Nat := 118140960795 + 405701 * 2 ^ 59
def prefixEnd_405701 : Nat := 4983230072969 + 3 ^ 40 * 405701 * 2
def baseEnd_405701 : Nat := 208319615009822426671721

theorem tailTrace_405701 : CollatzResearch.WordTrace tailWord_405701 prefixEnd_405701 208319615009822426671721 := by
  unfold tailWord_405701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14797131103222040059592957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9864754068814693373061971 14797131103222040059592957)
  ·
    refine ⟨5548924163708265022347359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14797131103222040059592957 5548924163708265022347359)
    ·
      refine ⟨8323386245562397533521039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5548924163708265022347359 8323386245562397533521039)
      ·
        refine ⟨12485079368343596300281559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8323386245562397533521039 12485079368343596300281559)
        ·
          refine ⟨18727619052515394450422339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12485079368343596300281559 18727619052515394450422339)
          ·
            refine ⟨28091428578773091675633509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18727619052515394450422339 28091428578773091675633509)
            ·
              refine ⟨5267142858519954689181283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28091428578773091675633509 5267142858519954689181283)
              ·
                refine ⟨7900714287779932033771925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5267142858519954689181283 7900714287779932033771925)
                ·
                  refine ⟨370345982239684314083059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7900714287779932033771925 370345982239684314083059)
                  ·
                    refine ⟨555518973359526471124589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370345982239684314083059 555518973359526471124589)
                    ·
                      refine ⟨208319615009822426671721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 555518973359526471124589 208319615009822426671721)
                      ·
                        rfl

theorem cell23_405701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_405701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405701 prefixEnd_405701 := by exact prefixLift 405701
  have htrace : WordTrace (prefixWord ++ tailWord_405701) baseStart_405701 baseEnd_405701 := by
    simpa [prefixWord, tailWord_405701, baseEnd_405701] using wordTrace_append hprefix tailTrace_405701
  have hstable : (prefixWord ++ tailWord_405701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405701).length < 2 ^ (prefixWord ++ tailWord_405701).sum := by decide
  have hdescent : baseEnd_405701 < baseStart_405701 := by decide
  rcases family_descends (prefixWord ++ tailWord_405701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405735 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_405735 : Nat := 118140960795 + 405735 * 2 ^ 59
def prefixEnd_405735 : Nat := 4983230072969 + 3 ^ 40 * 405735 * 2
def baseEnd_405735 : Nat := 208337073352075293646565

theorem tailTrace_405735 : CollatzResearch.WordTrace tailWord_405735 prefixEnd_405735 208337073352075293646565 := by
  unfold tailWord_405735
  simp only [CollatzResearch.WordTrace]
  refine ⟨14798371185098863866330659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9865580790065909244220439 14798371185098863866330659)
  ·
    refine ⟨22197556777648295799495989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14798371185098863866330659 22197556777648295799495989)
    ·
      refine ⟨2081020947904527731202749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22197556777648295799495989 2081020947904527731202749)
      ·
        refine ⟨780382855464197899201031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2081020947904527731202749 780382855464197899201031)
        ·
          refine ⟨1170574283196296848801547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780382855464197899201031 1170574283196296848801547)
          ·
            refine ⟨1755861424794445273202321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1170574283196296848801547 1755861424794445273202321)
            ·
              refine ⟨1316896068595833954901741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1755861424794445273202321 1316896068595833954901741)
              ·
                refine ⟨493836025723437733088153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316896068595833954901741 493836025723437733088153)
                ·
                  refine ⟨370377019292578299816115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 493836025723437733088153 370377019292578299816115)
                  ·
                    refine ⟨555565528938867449724173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370377019292578299816115 555565528938867449724173)
                    ·
                      refine ⟨208337073352075293646565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 555565528938867449724173 208337073352075293646565)
                      ·
                        rfl

theorem cell23_405735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_405735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405735 prefixEnd_405735 := by exact prefixLift 405735
  have htrace : WordTrace (prefixWord ++ tailWord_405735) baseStart_405735 baseEnd_405735 := by
    simpa [prefixWord, tailWord_405735, baseEnd_405735] using wordTrace_append hprefix tailTrace_405735
  have hstable : (prefixWord ++ tailWord_405735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405735).length < 2 ^ (prefixWord ++ tailWord_405735).sum := by decide
  have hdescent : baseEnd_405735 < baseStart_405735 := by decide
  rcases family_descends (prefixWord ++ tailWord_405735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405744 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_405744 : Nat := 118140960795 + 405744 * 2 ^ 59
def prefixEnd_405744 : Nat := 4983230072969 + 3 ^ 40 * 405744 * 2
def baseEnd_405744 : Nat := 208341694677965758434023

theorem tailTrace_405744 : CollatzResearch.WordTrace tailWord_405744 prefixEnd_405744 208341694677965758434023 := by
  unfold tailWord_405744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7399349721033129201704143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9865799628044172268938857 7399349721033129201704143)
  ·
    refine ⟨11099024581549693802556215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7399349721033129201704143 11099024581549693802556215)
    ·
      refine ⟨16648536872324540703834323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11099024581549693802556215 16648536872324540703834323)
      ·
        refine ⟨24972805308486811055751485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16648536872324540703834323 24972805308486811055751485)
        ·
          refine ⟨9364801990682554145906807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24972805308486811055751485 9364801990682554145906807)
          ·
            refine ⟨14047202986023831218860211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9364801990682554145906807 14047202986023831218860211)
            ·
              refine ⟨21070804479035746828290317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14047202986023831218860211 21070804479035746828290317)
              ·
                refine ⟨7901551679638405060608869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21070804479035746828290317 7901551679638405060608869)
                ·
                  refine ⟨1481540939932200948864163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7901551679638405060608869 1481540939932200948864163)
                  ·
                    refine ⟨2222311409898301423296245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1481540939932200948864163 2222311409898301423296245)
                    ·
                      refine ⟨208341694677965758434023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2222311409898301423296245 208341694677965758434023)
                      ·
                        rfl

theorem cell23_405744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_405744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405744 prefixEnd_405744 := by exact prefixLift 405744
  have htrace : WordTrace (prefixWord ++ tailWord_405744) baseStart_405744 baseEnd_405744 := by
    simpa [prefixWord, tailWord_405744, baseEnd_405744] using wordTrace_append hprefix tailTrace_405744
  have hstable : (prefixWord ++ tailWord_405744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405744).length < 2 ^ (prefixWord ++ tailWord_405744).sum := by decide
  have hdescent : baseEnd_405744 < baseStart_405744 := by decide
  rcases family_descends (prefixWord ++ tailWord_405744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405762 : List Nat := [3, 4, 1, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_405762 : Nat := 118140960795 + 405762 * 2 ^ 59
def prefixEnd_405762 : Nat := 4983230072969 + 3 ^ 40 * 405762 * 2
def baseEnd_405762 : Nat := 208350937329746688008941

theorem tailTrace_405762 : CollatzResearch.WordTrace tailWord_405762 prefixEnd_405762 208350937329746688008941 := by
  unfold tailWord_405762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3699838989000261869390885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9866237304000698318375693 3699838989000261869390885)
  ·
    refine ⟨693719810437549100510791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3699838989000261869390885 693719810437549100510791)
    ·
      refine ⟨1040579715656323650766187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693719810437549100510791 1040579715656323650766187)
      ·
        refine ⟨1560869573484485476149281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040579715656323650766187 1560869573484485476149281)
        ·
          refine ⟨1170652180113364107111961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1560869573484485476149281 1170652180113364107111961)
          ·
            refine ⟨877989135085023080333971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170652180113364107111961 877989135085023080333971)
            ·
              refine ⟨1316983702627534620500957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 877989135085023080333971 1316983702627534620500957)
              ·
                refine ⟨493868888485325482687859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1316983702627534620500957 493868888485325482687859)
                ·
                  refine ⟨740803332727988224031789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 493868888485325482687859 740803332727988224031789)
                  ·
                    refine ⟨277801249772995584011921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 740803332727988224031789 277801249772995584011921)
                    ·
                      refine ⟨208350937329746688008941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 277801249772995584011921 208350937329746688008941)
                      ·
                        rfl

theorem cell23_405762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_405762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405762 prefixEnd_405762 := by exact prefixLift 405762
  have htrace : WordTrace (prefixWord ++ tailWord_405762) baseStart_405762 baseEnd_405762 := by
    simpa [prefixWord, tailWord_405762, baseEnd_405762] using wordTrace_append hprefix tailTrace_405762
  have hstable : (prefixWord ++ tailWord_405762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405762).length < 2 ^ (prefixWord ++ tailWord_405762).sum := by decide
  have hdescent : baseEnd_405762 < baseStart_405762 := by decide
  rcases family_descends (prefixWord ++ tailWord_405762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405811 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 2, 5]
def baseStart_405811 : Nat := 118140960795 + 405811 * 2 ^ 59
def prefixEnd_405811 : Nat := 4983230072969 + 3 ^ 40 * 405811 * 2
def baseEnd_405811 : Nat := 69458699293938998765405

theorem tailTrace_405811 : CollatzResearch.WordTrace tailWord_405811 prefixEnd_405811 69458699293938998765405 := by
  unfold tailWord_405811
  simp only [CollatzResearch.WordTrace]
  refine ⟨14801143132823528846097287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9867428755215685897398191 14801143132823528846097287)
  ·
    refine ⟨22201714699235293269145931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14801143132823528846097287 22201714699235293269145931)
    ·
      refine ⟨33302572048852939903718897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22201714699235293269145931 33302572048852939903718897)
      ·
        refine ⟨24976929036639704927789173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33302572048852939903718897 24976929036639704927789173)
        ·
          refine ⟨2341587097184972336980235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24976929036639704927789173 2341587097184972336980235)
          ·
            refine ⟨3512380645777458505470353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2341587097184972336980235 3512380645777458505470353)
            ·
              refine ⟨2634285484333093879102765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3512380645777458505470353 2634285484333093879102765)
              ·
                refine ⟨987857056624910204663537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2634285484333093879102765 987857056624910204663537)
                ·
                  refine ⟨740892792468682653497653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 987857056624910204663537 740892792468682653497653)
                  ·
                    refine ⟨69458699293938998765405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 740892792468682653497653 69458699293938998765405)
                    ·
                      rfl

theorem cell23_405811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 2, 5].length) (baseStart_405811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405811 prefixEnd_405811 := by exact prefixLift 405811
  have htrace : WordTrace (prefixWord ++ tailWord_405811) baseStart_405811 baseEnd_405811 := by
    simpa [prefixWord, tailWord_405811, baseEnd_405811] using wordTrace_append hprefix tailTrace_405811
  have hstable : (prefixWord ++ tailWord_405811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405811).length < 2 ^ (prefixWord ++ tailWord_405811).sum := by decide
  have hdescent : baseEnd_405811 < baseStart_405811 := by decide
  rcases family_descends (prefixWord ++ tailWord_405811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405951 : List Nat := [1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4]
def baseStart_405951 : Nat := 118140960795 + 405951 * 2 ^ 59
def prefixEnd_405951 : Nat := 4983230072969 + 3 ^ 40 * 405951 * 2
def baseEnd_405951 : Nat := 208447985173446448545571

theorem tailTrace_405951 : CollatzResearch.WordTrace tailWord_405951 prefixEnd_405951 208447985173446448545571 := by
  unfold tailWord_405951
  simp only [CollatzResearch.WordTrace]
  refine ⟨14806249352316332756193707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9870832901544221837462471 14806249352316332756193707)
  ·
    refine ⟨22209374028474499134290561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14806249352316332756193707 22209374028474499134290561)
    ·
      refine ⟨16657030521355874350717921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22209374028474499134290561 16657030521355874350717921)
      ·
        refine ⟨12492772891016905763038441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16657030521355874350717921 12492772891016905763038441)
        ·
          refine ⟨9369579668262679322278831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12492772891016905763038441 9369579668262679322278831)
          ·
            refine ⟨14054369502394018983418247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9369579668262679322278831 14054369502394018983418247)
            ·
              refine ⟨21081554253591028475127371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14054369502394018983418247 21081554253591028475127371)
              ·
                refine ⟨31622331380386542712691057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21081554253591028475127371 31622331380386542712691057)
                ·
                  refine ⟨23716748535289907034518293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31622331380386542712691057 23716748535289907034518293)
                  ·
                    refine ⟨1111722587591714392243045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23716748535289907034518293 1111722587591714392243045)
                    ·
                      refine ⟨208447985173446448545571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1111722587591714392243045 208447985173446448545571)
                      ·
                        rfl

theorem cell23_405951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_405951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405951 prefixEnd_405951 := by exact prefixLift 405951
  have htrace : WordTrace (prefixWord ++ tailWord_405951) baseStart_405951 baseEnd_405951 := by
    simpa [prefixWord, tailWord_405951, baseEnd_405951] using wordTrace_append hprefix tailTrace_405951
  have hstable : (prefixWord ++ tailWord_405951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405951).length < 2 ^ (prefixWord ++ tailWord_405951).sum := by decide
  have hdescent : baseEnd_405951 < baseStart_405951 := by decide
  rcases family_descends (prefixWord ++ tailWord_405951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405972 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 1, 1, 4]
def baseStart_405972 : Nat := 118140960795 + 405972 * 2 ^ 59
def prefixEnd_405972 : Nat := 4983230072969 + 3 ^ 40 * 405972 * 2
def baseEnd_405972 : Nat := 208458768267190866382975

theorem tailTrace_405972 : CollatzResearch.WordTrace tailWord_405972 prefixEnd_405972 208458768267190866382975 := by
  unfold tailWord_405972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7403507642620126671354085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9871343523493502228472113 7403507642620126671354085)
  ·
    refine ⟨1388157682991273750878891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7403507642620126671354085 1388157682991273750878891)
    ·
      refine ⟨2082236524486910626318337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388157682991273750878891 2082236524486910626318337)
      ·
        refine ⟨1561677393365182969738753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2082236524486910626318337 1561677393365182969738753)
        ·
          refine ⟨1171258045023887227304065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1561677393365182969738753 1171258045023887227304065)
          ·
            refine ⟨878443533767915420478049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1171258045023887227304065 878443533767915420478049)
            ·
              refine ⟨658832650325936565358537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878443533767915420478049 658832650325936565358537)
              ·
                refine ⟨494124487744452424018903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 658832650325936565358537 494124487744452424018903)
                ·
                  refine ⟨741186731616678636028355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494124487744452424018903 741186731616678636028355)
                  ·
                    refine ⟨1111780097425017954042533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 741186731616678636028355 1111780097425017954042533)
                    ·
                      refine ⟨208458768267190866382975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1111780097425017954042533 208458768267190866382975)
                      ·
                        rfl

theorem cell23_405972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_405972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_405972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_405972 prefixEnd_405972 := by exact prefixLift 405972
  have htrace : WordTrace (prefixWord ++ tailWord_405972) baseStart_405972 baseEnd_405972 := by
    simpa [prefixWord, tailWord_405972, baseEnd_405972] using wordTrace_append hprefix tailTrace_405972
  have hstable : (prefixWord ++ tailWord_405972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405972).length < 2 ^ (prefixWord ++ tailWord_405972).sum := by decide
  have hdescent : baseEnd_405972 < baseStart_405972 := by decide
  rcases family_descends (prefixWord ++ tailWord_405972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406015 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 3, 3, 2]
def baseStart_406015 : Nat := 118140960795 + 406015 * 2 ^ 59
def prefixEnd_406015 : Nat := 4983230072969 + 3 ^ 40 * 406015 * 2
def baseEnd_406015 : Nat := 208480847935334198145277

theorem tailTrace_406015 : CollatzResearch.WordTrace tailWord_406015 prefixEnd_406015 208480847935334198145277 := by
  unfold tailWord_406015
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808583624084471686523499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872389082722981124348999 14808583624084471686523499)
  ·
    refine ⟨22212875436126707529785249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14808583624084471686523499 22212875436126707529785249)
    ·
      refine ⟨16659656577095030647338937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22212875436126707529785249 16659656577095030647338937)
      ·
        refine ⟨12494742432821272985504203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16659656577095030647338937 12494742432821272985504203)
        ·
          refine ⟨18742113649231909478256305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12494742432821272985504203 18742113649231909478256305)
          ·
            refine ⟨14056585236923932108692229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18742113649231909478256305 14056585236923932108692229)
            ·
              refine ⟨2635609731923237270379793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14056585236923932108692229 2635609731923237270379793)
              ·
                refine ⟨1976707298942427952784845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2635609731923237270379793 1976707298942427952784845)
                ·
                  refine ⟨741265237103410482294317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1976707298942427952784845 741265237103410482294317)
                  ·
                    refine ⟨277974463913778930860369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741265237103410482294317 277974463913778930860369)
                    ·
                      refine ⟨208480847935334198145277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 277974463913778930860369 208480847935334198145277)
                      ·
                        rfl

theorem cell23_406015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_406015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406015 prefixEnd_406015 := by exact prefixLift 406015
  have htrace : WordTrace (prefixWord ++ tailWord_406015) baseStart_406015 baseEnd_406015 := by
    simpa [prefixWord, tailWord_406015, baseEnd_406015] using wordTrace_append hprefix tailTrace_406015
  have hstable : (prefixWord ++ tailWord_406015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406015).length < 2 ^ (prefixWord ++ tailWord_406015).sum := by decide
  have hdescent : baseEnd_406015 < baseStart_406015 := by decide
  rcases family_descends (prefixWord ++ tailWord_406015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406049 : List Nat := [1, 2, 3, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_406049 : Nat := 118140960795 + 406049 * 2 ^ 59
def prefixEnd_406049 : Nat := 4983230072969 + 3 ^ 40 * 406049 * 2
def baseEnd_406049 : Nat := 208498306277587065120121

theorem tailTrace_406049 : CollatzResearch.WordTrace tailWord_406049 prefixEnd_406049 208498306277587065120121 := by
  unfold tailWord_406049
  simp only [CollatzResearch.WordTrace]
  refine ⟨14809823705961295493261201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9873215803974196995507467 14809823705961295493261201)
  ·
    refine ⟨11107367779470971619945901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14809823705961295493261201 11107367779470971619945901)
    ·
      refine ⟨4165262917301614357479713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11107367779470971619945901 4165262917301614357479713)
      ·
        refine ⟨3123947187976210768109785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4165262917301614357479713 3123947187976210768109785)
        ·
          refine ⟨2342960390982158076082339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123947187976210768109785 2342960390982158076082339)
          ·
            refine ⟨3514440586473237114123509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2342960390982158076082339 3514440586473237114123509)
            ·
              refine ⟨329478804981865979449079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3514440586473237114123509 329478804981865979449079)
              ·
                refine ⟨494218207472798969173619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329478804981865979449079 494218207472798969173619)
                ·
                  refine ⟨741327311209198453760429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494218207472798969173619 741327311209198453760429)
                  ·
                    refine ⟨277997741703449420160161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741327311209198453760429 277997741703449420160161)
                    ·
                      refine ⟨208498306277587065120121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 277997741703449420160161 208498306277587065120121)
                      ·
                        rfl

theorem cell23_406049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_406049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406049 prefixEnd_406049 := by exact prefixLift 406049
  have htrace : WordTrace (prefixWord ++ tailWord_406049) baseStart_406049 baseEnd_406049 := by
    simpa [prefixWord, tailWord_406049, baseEnd_406049] using wordTrace_append hprefix tailTrace_406049
  have hstable : (prefixWord ++ tailWord_406049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406049).length < 2 ^ (prefixWord ++ tailWord_406049).sum := by decide
  have hdescent : baseEnd_406049 < baseStart_406049 := by decide
  rcases family_descends (prefixWord ++ tailWord_406049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406138 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_406138 : Nat := 118140960795 + 406138 * 2 ^ 59
def prefixEnd_406138 : Nat := 4983230072969 + 3 ^ 40 * 406138 * 2
def baseEnd_406138 : Nat := 208544006055837216907211

theorem tailTrace_406138 : CollatzResearch.WordTrace tailWord_406138 prefixEnd_406138 208544006055837216907211 := by
  unfold tailWord_406138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703267450659715923312767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9875379868425909128834045 3703267450659715923312767)
  ·
    refine ⟨5554901175989573884969151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703267450659715923312767 5554901175989573884969151)
    ·
      refine ⟨8332351763984360827453727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554901175989573884969151 8332351763984360827453727)
      ·
        refine ⟨12498527645976541241180591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8332351763984360827453727 12498527645976541241180591)
        ·
          refine ⟨18747791468964811861770887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12498527645976541241180591 18747791468964811861770887)
          ·
            refine ⟨28121687203447217792656331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18747791468964811861770887 28121687203447217792656331)
            ·
              refine ⟨42182530805170826688984497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28121687203447217792656331 42182530805170826688984497)
              ·
                refine ⟨31636898103878120016738373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42182530805170826688984497 31636898103878120016738373)
                ·
                  refine ⟨5931918394477147503138445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31636898103878120016738373 5931918394477147503138445)
                  ·
                    refine ⟨2224469397928930313676917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5931918394477147503138445 2224469397928930313676917)
                    ·
                      refine ⟨208544006055837216907211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2224469397928930313676917 208544006055837216907211)
                      ·
                        rfl

theorem cell23_406138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_406138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406138 prefixEnd_406138 := by exact prefixLift 406138
  have htrace : WordTrace (prefixWord ++ tailWord_406138) baseStart_406138 baseEnd_406138 := by
    simpa [prefixWord, tailWord_406138, baseEnd_406138] using wordTrace_append hprefix tailTrace_406138
  have hstable : (prefixWord ++ tailWord_406138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406138).length < 2 ^ (prefixWord ++ tailWord_406138).sum := by decide
  have hdescent : baseEnd_406138 < baseStart_406138 := by decide
  rcases family_descends (prefixWord ++ tailWord_406138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406172 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_406172 : Nat := 118140960795 + 406172 * 2 ^ 59
def prefixEnd_406172 : Nat := 4983230072969 + 3 ^ 40 * 406172 * 2
def baseEnd_406172 : Nat := 208561464398090083882055

theorem tailTrace_406172 : CollatzResearch.WordTrace tailWord_406172 prefixEnd_406172 208561464398090083882055 := by
  unfold tailWord_406172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7407154942257843749994385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9876206589677124999992513 7407154942257843749994385)
  ·
    refine ⟨5555366206693382812495789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7407154942257843749994385 5555366206693382812495789)
    ·
      refine ⟨2083262327510018554685921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5555366206693382812495789 2083262327510018554685921)
      ·
        refine ⟨1562446745632513916014441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2083262327510018554685921 1562446745632513916014441)
        ·
          refine ⟨1171835059224385437010831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562446745632513916014441 1171835059224385437010831)
          ·
            refine ⟨1757752588836578155516247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171835059224385437010831 1757752588836578155516247)
            ·
              refine ⟨2636628883254867233274371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757752588836578155516247 2636628883254867233274371)
              ·
                refine ⟨3954943324882300849911557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636628883254867233274371 3954943324882300849911557)
                ·
                  refine ⟨741551873415431409358417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3954943324882300849911557 741551873415431409358417)
                  ·
                    refine ⟨556163905061573557018813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 741551873415431409358417 556163905061573557018813)
                    ·
                      refine ⟨208561464398090083882055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 556163905061573557018813 208561464398090083882055)
                      ·
                        rfl

theorem cell23_406172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_406172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406172 prefixEnd_406172 := by exact prefixLift 406172
  have htrace : WordTrace (prefixWord ++ tailWord_406172) baseStart_406172 baseEnd_406172 := by
    simpa [prefixWord, tailWord_406172, baseEnd_406172] using wordTrace_append hprefix tailTrace_406172
  have hstable : (prefixWord ++ tailWord_406172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406172).length < 2 ^ (prefixWord ++ tailWord_406172).sum := by decide
  have hdescent : baseEnd_406172 < baseStart_406172 := by decide
  rcases family_descends (prefixWord ++ tailWord_406172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406202 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_406202 : Nat := 118140960795 + 406202 * 2 ^ 59
def prefixEnd_406202 : Nat := 4983230072969 + 3 ^ 40 * 406202 * 2
def baseEnd_406202 : Nat := 208576868817724966506917

theorem tailTrace_406202 : CollatzResearch.WordTrace tailWord_406202 prefixEnd_406202 208576868817724966506917 := by
  unfold tailWord_406202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703851018601750655895215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9876936049604668415720573 3703851018601750655895215)
  ·
    refine ⟨5555776527902625983842823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3703851018601750655895215 5555776527902625983842823)
    ·
      refine ⟨8333664791853938975764235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5555776527902625983842823 8333664791853938975764235)
      ·
        refine ⟨12500497187780908463646353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8333664791853938975764235 12500497187780908463646353)
        ·
          refine ⟨9375372890835681347734765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12500497187780908463646353 9375372890835681347734765)
          ·
            refine ⟨3515764834063380505400537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9375372890835681347734765 3515764834063380505400537)
            ·
              refine ⟨2636823625547535379050403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3515764834063380505400537 2636823625547535379050403)
              ·
                refine ⟨3955235438321303068575605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2636823625547535379050403 3955235438321303068575605)
                ·
                  refine ⟨370803322342622162678963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3955235438321303068575605 370803322342622162678963)
                  ·
                    refine ⟨556204983513933244018445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 370803322342622162678963 556204983513933244018445)
                    ·
                      refine ⟨208576868817724966506917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 556204983513933244018445 208576868817724966506917)
                      ·
                        rfl

theorem cell23_406202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_406202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406202 prefixEnd_406202 := by exact prefixLift 406202
  have htrace : WordTrace (prefixWord ++ tailWord_406202) baseStart_406202 baseEnd_406202 := by
    simpa [prefixWord, tailWord_406202, baseEnd_406202] using wordTrace_append hprefix tailTrace_406202
  have hstable : (prefixWord ++ tailWord_406202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406202).length < 2 ^ (prefixWord ++ tailWord_406202).sum := by decide
  have hdescent : baseEnd_406202 < baseStart_406202 := by decide
  rcases family_descends (prefixWord ++ tailWord_406202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406315 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4]
def baseStart_406315 : Nat := 118140960795 + 406315 * 2 ^ 59
def prefixEnd_406315 : Nat := 4983230072969 + 3 ^ 40 * 406315 * 2
def baseEnd_406315 : Nat := 208634892131683024393897

theorem tailTrace_406315 : CollatzResearch.WordTrace tailWord_406315 prefixEnd_406315 208634892131683024393897 := by
  unfold tailWord_406315
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819525522997622922444399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9879683681998415281629599 14819525522997622922444399)
  ·
    refine ⟨22229288284496434383666599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14819525522997622922444399 22229288284496434383666599)
    ·
      refine ⟨33343932426744651575499899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22229288284496434383666599 33343932426744651575499899)
      ·
        refine ⟨50015898640116977363249849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33343932426744651575499899 50015898640116977363249849)
        ·
          refine ⟨37511923980087733022437387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50015898640116977363249849 37511923980087733022437387)
          ·
            refine ⟨56267885970131599533656081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37511923980087733022437387 56267885970131599533656081)
            ·
              refine ⟨42200914477598699650242061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56267885970131599533656081 42200914477598699650242061)
              ·
                refine ⟨15825342929099512368840773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42200914477598699650242061 15825342929099512368840773)
                ·
                  refine ⟨2967251799206158569157645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15825342929099512368840773 2967251799206158569157645)
                  ·
                    refine ⟨1112719424702309463434117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2967251799206158569157645 1112719424702309463434117)
                    ·
                      refine ⟨208634892131683024393897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1112719424702309463434117 208634892131683024393897)
                      ·
                        rfl

theorem cell23_406315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 4].length) (baseStart_406315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406315 prefixEnd_406315 := by exact prefixLift 406315
  have htrace : WordTrace (prefixWord ++ tailWord_406315) baseStart_406315 baseEnd_406315 := by
    simpa [prefixWord, tailWord_406315, baseEnd_406315] using wordTrace_append hprefix tailTrace_406315
  have hstable : (prefixWord ++ tailWord_406315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406315).length < 2 ^ (prefixWord ++ tailWord_406315).sum := by decide
  have hdescent : baseEnd_406315 < baseStart_406315 := by decide
  rcases family_descends (prefixWord ++ tailWord_406315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406370 : List Nat := [3, 3, 2, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_406370 : Nat := 118140960795 + 406370 * 2 ^ 59
def prefixEnd_406370 : Nat := 4983230072969 + 3 ^ 40 * 406370 * 2
def baseEnd_406370 : Nat := 208663133567680309206145

theorem tailTrace_406370 : CollatzResearch.WordTrace tailWord_406370 prefixEnd_406370 208663133567680309206145 := by
  unfold tailWord_406370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3705382884449591828924141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9881021025198911543797709 3705382884449591828924141)
  ·
    refine ⟨1389518581668596935846553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3705382884449591828924141 1389518581668596935846553)
    ·
      refine ⟨1042138936251447701884915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1389518581668596935846553 1042138936251447701884915)
      ·
        refine ⟨1563208404377171552827373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042138936251447701884915 1563208404377171552827373)
        ·
          refine ⟨586203151641439332310265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1563208404377171552827373 586203151641439332310265)
          ·
            refine ⟨439652363731079499232699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586203151641439332310265 439652363731079499232699)
            ·
              refine ⟨659478545596619248849049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439652363731079499232699 659478545596619248849049)
              ·
                refine ⟨494608909197464436636787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 659478545596619248849049 494608909197464436636787)
                ·
                  refine ⟨741913363796196654955181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494608909197464436636787 741913363796196654955181)
                  ·
                    refine ⟨278217511423573745608193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 741913363796196654955181 278217511423573745608193)
                    ·
                      refine ⟨208663133567680309206145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278217511423573745608193 208663133567680309206145)
                      ·
                        rfl

theorem cell23_406370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_406370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406370 prefixEnd_406370 := by exact prefixLift 406370
  have htrace : WordTrace (prefixWord ++ tailWord_406370) baseStart_406370 baseEnd_406370 := by
    simpa [prefixWord, tailWord_406370, baseEnd_406370] using wordTrace_append hprefix tailTrace_406370
  have hstable : (prefixWord ++ tailWord_406370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406370).length < 2 ^ (prefixWord ++ tailWord_406370).sum := by decide
  have hdescent : baseEnd_406370 < baseStart_406370 := by decide
  rcases family_descends (prefixWord ++ tailWord_406370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406409 : List Nat := [1, 2, 1, 1, 5, 2, 1, 1, 2, 5, 2]
def baseStart_406409 : Nat := 118140960795 + 406409 * 2 ^ 59
def prefixEnd_406409 : Nat := 4983230072969 + 3 ^ 40 * 406409 * 2
def baseEnd_406409 : Nat := 208683159313205656618465

theorem tailTrace_406409 : CollatzResearch.WordTrace tailWord_406409 prefixEnd_406409 208683159313205656618465 := by
  unfold tailWord_406409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14822953984657076976366281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9881969323104717984244187 14822953984657076976366281)
  ·
    refine ⟨11117215488492807732274711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14822953984657076976366281 11117215488492807732274711)
    ·
      refine ⟨16675823232739211598412067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11117215488492807732274711 16675823232739211598412067)
      ·
        refine ⟨25013734849108817397618101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16675823232739211598412067 25013734849108817397618101)
        ·
          refine ⟨2345037642103951631026697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25013734849108817397618101 2345037642103951631026697)
          ·
            refine ⟨1758778231577963723270023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2345037642103951631026697 1758778231577963723270023)
            ·
              refine ⟨2638167347366945584905035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758778231577963723270023 2638167347366945584905035)
              ·
                refine ⟨3957251021050418377357553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2638167347366945584905035 3957251021050418377357553)
                ·
                  refine ⟨2967938265787813783018165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3957251021050418377357553 2967938265787813783018165)
                  ·
                    refine ⟨278244212417607542157953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2967938265787813783018165 278244212417607542157953)
                    ·
                      refine ⟨208683159313205656618465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278244212417607542157953 208683159313205656618465)
                      ·
                        rfl

theorem cell23_406409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 5, 2].length) (baseStart_406409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406409 prefixEnd_406409 := by exact prefixLift 406409
  have htrace : WordTrace (prefixWord ++ tailWord_406409) baseStart_406409 baseEnd_406409 := by
    simpa [prefixWord, tailWord_406409, baseEnd_406409] using wordTrace_append hprefix tailTrace_406409
  have hstable : (prefixWord ++ tailWord_406409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406409).length < 2 ^ (prefixWord ++ tailWord_406409).sum := by decide
  have hdescent : baseEnd_406409 < baseStart_406409 := by decide
  rcases family_descends (prefixWord ++ tailWord_406409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406412 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_406412 : Nat := 118140960795 + 406412 * 2 ^ 59
def prefixEnd_406412 : Nat := 4983230072969 + 3 ^ 40 * 406412 * 2
def baseEnd_406412 : Nat := 208684699755169144880951

theorem tailTrace_406412 : CollatzResearch.WordTrace tailWord_406412 prefixEnd_406412 208684699755169144880951 := by
  unfold tailWord_406412
  simp only [CollatzResearch.WordTrace]
  refine ⟨7411531701823104244362745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9882042269097472325816993 7411531701823104244362745)
  ·
    refine ⟨5558648776367328183272059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7411531701823104244362745 5558648776367328183272059)
    ·
      refine ⟨8337973164550992274908089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558648776367328183272059 8337973164550992274908089)
      ·
        refine ⟨6253479873413244206181067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8337973164550992274908089 6253479873413244206181067)
        ·
          refine ⟨9380219810119866309271601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6253479873413244206181067 9380219810119866309271601)
          ·
            refine ⟨7035164857589899731953701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9380219810119866309271601 7035164857589899731953701)
            ·
              refine ⟨1319093410798106199741319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7035164857589899731953701 1319093410798106199741319)
              ·
                refine ⟨1978640116197159299611979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319093410798106199741319 1978640116197159299611979)
                ·
                  refine ⟨2967960174295738949417969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1978640116197159299611979 2967960174295738949417969)
                  ·
                    refine ⟨2225970130721804212063477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2967960174295738949417969 2225970130721804212063477)
                    ·
                      refine ⟨208684699755169144880951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2225970130721804212063477 208684699755169144880951)
                      ·
                        rfl

theorem cell23_406412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_406412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406412 prefixEnd_406412 := by exact prefixLift 406412
  have htrace : WordTrace (prefixWord ++ tailWord_406412) baseStart_406412 baseEnd_406412 := by
    simpa [prefixWord, tailWord_406412, baseEnd_406412] using wordTrace_append hprefix tailTrace_406412
  have hstable : (prefixWord ++ tailWord_406412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406412).length < 2 ^ (prefixWord ++ tailWord_406412).sum := by decide
  have hdescent : baseEnd_406412 < baseStart_406412 := by decide
  rcases family_descends (prefixWord ++ tailWord_406412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406517 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 3, 4]
def baseStart_406517 : Nat := 118140960795 + 406517 * 2 ^ 59
def prefixEnd_406517 : Nat := 4983230072969 + 3 ^ 40 * 406517 * 2
def baseEnd_406517 : Nat := 69579538407963744689323

theorem tailTrace_406517 : CollatzResearch.WordTrace tailWord_406517 prefixEnd_406517 69579538407963744689323 := by
  unfold tailWord_406517
  simp only [CollatzResearch.WordTrace]
  refine ⟨14826893068265811421297805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9884595378843874280865203 14826893068265811421297805)
  ·
    refine ⟨5560084900599679282986677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14826893068265811421297805 5560084900599679282986677)
    ·
      refine ⟨521257959431219932780001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5560084900599679282986677 521257959431219932780001)
      ·
        refine ⟨390943469573414949585001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521257959431219932780001 390943469573414949585001)
        ·
          refine ⟨293207602180061212188751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390943469573414949585001 293207602180061212188751)
          ·
            refine ⟨439811403270091818283127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293207602180061212188751 439811403270091818283127)
            ·
              refine ⟨659717104905137727424691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439811403270091818283127 659717104905137727424691)
              ·
                refine ⟨989575657357706591137037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659717104905137727424691 989575657357706591137037)
                ·
                  refine ⟨371090871509139971676389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 989575657357706591137037 371090871509139971676389)
                  ·
                    refine ⟨69579538407963744689323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371090871509139971676389 69579538407963744689323)
                    ·
                      rfl

theorem cell23_406517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_406517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406517 prefixEnd_406517 := by exact prefixLift 406517
  have htrace : WordTrace (prefixWord ++ tailWord_406517) baseStart_406517 baseEnd_406517 := by
    simpa [prefixWord, tailWord_406517, baseEnd_406517] using wordTrace_append hprefix tailTrace_406517
  have hstable : (prefixWord ++ tailWord_406517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406517).length < 2 ^ (prefixWord ++ tailWord_406517).sum := by decide
  have hdescent : baseEnd_406517 < baseStart_406517 := by decide
  rcases family_descends (prefixWord ++ tailWord_406517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406556 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_406556 : Nat := 118140960795 + 406556 * 2 ^ 59
def prefixEnd_406556 : Nat := 4983230072969 + 3 ^ 40 * 406556 * 2
def baseEnd_406556 : Nat := 69586213656472193826763

theorem tailTrace_406556 : CollatzResearch.WordTrace tailWord_406556 prefixEnd_406556 69586213656472193826763 := by
  unfold tailWord_406556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414157757562260540983761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9885543676749680721311681 7414157757562260540983761)
  ·
    refine ⟨5560618318171695405737821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7414157757562260540983761 5560618318171695405737821)
    ·
      refine ⟨2085231869314385777151683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5560618318171695405737821 2085231869314385777151683)
      ·
        refine ⟨3127847803971578665727525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2085231869314385777151683 3127847803971578665727525)
        ·
          refine ⟨586471463244670999823911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3127847803971578665727525 586471463244670999823911)
          ·
            refine ⟨879707194867006499735867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586471463244670999823911 879707194867006499735867)
            ·
              refine ⟨1319560792300509749603801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879707194867006499735867 1319560792300509749603801)
              ·
                refine ⟨989670594225382312202851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1319560792300509749603801 989670594225382312202851)
                ·
                  refine ⟨1484505891338073468304277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989670594225382312202851 1484505891338073468304277)
                  ·
                    refine ⟨69586213656472193826763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1484505891338073468304277 69586213656472193826763)
                    ·
                      rfl

theorem cell23_406556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_406556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406556 prefixEnd_406556 := by exact prefixLift 406556
  have htrace : WordTrace (prefixWord ++ tailWord_406556) baseStart_406556 baseEnd_406556 := by
    simpa [prefixWord, tailWord_406556, baseEnd_406556] using wordTrace_append hprefix tailTrace_406556
  have hstable : (prefixWord ++ tailWord_406556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406556).length < 2 ^ (prefixWord ++ tailWord_406556).sum := by decide
  have hdescent : baseEnd_406556 < baseStart_406556 := by decide
  rcases family_descends (prefixWord ++ tailWord_406556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406559 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4]
def baseStart_406559 : Nat := 118140960795 + 406559 * 2 ^ 59
def prefixEnd_406559 : Nat := 4983230072969 + 3 ^ 40 * 406559 * 2
def baseEnd_406559 : Nat := 208760181411380069742775

theorem tailTrace_406559 : CollatzResearch.WordTrace tailWord_406559 prefixEnd_406559 208760181411380069742775 := by
  unfold tailWord_406559
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828424934113652594326731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9885616622742435062884487 14828424934113652594326731)
  ·
    refine ⟨22242637401170478891490097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14828424934113652594326731 22242637401170478891490097)
    ·
      refine ⟨16681978050877859168617573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22242637401170478891490097 16681978050877859168617573)
      ·
        refine ⟨3127870884539598594115795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16681978050877859168617573 3127870884539598594115795)
        ·
          refine ⟨4691806326809397891173693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3127870884539598594115795 4691806326809397891173693)
          ·
            refine ⟨1759427372553524209190135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4691806326809397891173693 1759427372553524209190135)
            ·
              refine ⟨2639141058830286313785203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759427372553524209190135 2639141058830286313785203)
              ·
                refine ⟨3958711588245429470677805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2639141058830286313785203 3958711588245429470677805)
                ·
                  refine ⟨1484516845592036051504177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3958711588245429470677805 1484516845592036051504177)
                  ·
                    refine ⟨1113387634194027038628133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484516845592036051504177 1113387634194027038628133)
                    ·
                      refine ⟨208760181411380069742775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1113387634194027038628133 208760181411380069742775)
                      ·
                        rfl

theorem cell23_406559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_406559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406559 prefixEnd_406559 := by exact prefixLift 406559
  have htrace : WordTrace (prefixWord ++ tailWord_406559) baseStart_406559 baseEnd_406559 := by
    simpa [prefixWord, tailWord_406559, baseEnd_406559] using wordTrace_append hprefix tailTrace_406559
  have hstable : (prefixWord ++ tailWord_406559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406559).length < 2 ^ (prefixWord ++ tailWord_406559).sum := by decide
  have hdescent : baseEnd_406559 < baseStart_406559 := by decide
  rcases family_descends (prefixWord ++ tailWord_406559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406560 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 1, 5]
def baseStart_406560 : Nat := 118140960795 + 406560 * 2 ^ 59
def prefixEnd_406560 : Nat := 4983230072969 + 3 ^ 40 * 406560 * 2
def baseEnd_406560 : Nat := 69586898297344855276757

theorem tailTrace_406560 : CollatzResearch.WordTrace tailWord_406560 prefixEnd_406560 69586898297344855276757 := by
  unfold tailWord_406560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7414230703555014882556567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9885640938073353176742089 7414230703555014882556567)
  ·
    refine ⟨11121346055332522323834851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7414230703555014882556567 11121346055332522323834851)
    ·
      refine ⟨16682019082998783485752277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11121346055332522323834851 16682019082998783485752277)
      ·
        refine ⟨390984822257783987947319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16682019082998783485752277 390984822257783987947319)
        ·
          refine ⟨586477233386675981920979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390984822257783987947319 586477233386675981920979)
          ·
            refine ⟨879715850080013972881469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586477233386675981920979 879715850080013972881469)
            ·
              refine ⟨329893443780005239830551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879715850080013972881469 329893443780005239830551)
              ·
                refine ⟨494840165670007859745827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329893443780005239830551 494840165670007859745827)
                ·
                  refine ⟨742260248505011789618741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494840165670007859745827 742260248505011789618741)
                  ·
                    refine ⟨69586898297344855276757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 742260248505011789618741 69586898297344855276757)
                    ·
                      rfl

theorem cell23_406560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_406560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406560 prefixEnd_406560 := by exact prefixLift 406560
  have htrace : WordTrace (prefixWord ++ tailWord_406560) baseStart_406560 baseEnd_406560 := by
    simpa [prefixWord, tailWord_406560, baseEnd_406560] using wordTrace_append hprefix tailTrace_406560
  have hstable : (prefixWord ++ tailWord_406560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406560).length < 2 ^ (prefixWord ++ tailWord_406560).sum := by decide
  have hdescent : baseEnd_406560 < baseStart_406560 := by decide
  rcases family_descends (prefixWord ++ tailWord_406560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406563 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 1, 1, 4]
def baseStart_406563 : Nat := 118140960795 + 406563 * 2 ^ 59
def prefixEnd_406563 : Nat := 4983230072969 + 3 ^ 40 * 406563 * 2
def baseEnd_406563 : Nat := 208762235333998054092757

theorem tailTrace_406563 : CollatzResearch.WordTrace tailWord_406563 prefixEnd_406563 208762235333998054092757 := by
  unfold tailWord_406563
  simp only [CollatzResearch.WordTrace]
  refine ⟨14828570826099161277472343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9885713884066107518314895 14828570826099161277472343)
  ·
    refine ⟨22242856239148741916208515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14828570826099161277472343 22242856239148741916208515)
    ·
      refine ⟨33364284358723112874312773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22242856239148741916208515 33364284358723112874312773)
      ·
        refine ⟨6255803317260583663933645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33364284358723112874312773 6255803317260583663933645)
        ·
          refine ⟨2345926243972718873975117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6255803317260583663933645 2345926243972718873975117)
          ·
            refine ⟨879722341489769577740669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2345926243972718873975117 879722341489769577740669)
            ·
              refine ⟨329895878058663591652751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879722341489769577740669 329895878058663591652751)
              ·
                refine ⟨494843817087995387479127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329895878058663591652751 494843817087995387479127)
                ·
                  refine ⟨742265725631993081218691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494843817087995387479127 742265725631993081218691)
                  ·
                    refine ⟨1113398588447989621828037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742265725631993081218691 1113398588447989621828037)
                    ·
                      refine ⟨208762235333998054092757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1113398588447989621828037 208762235333998054092757)
                      ·
                        rfl

theorem cell23_406563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_406563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406563 prefixEnd_406563 := by exact prefixLift 406563
  have htrace : WordTrace (prefixWord ++ tailWord_406563) baseStart_406563 baseEnd_406563 := by
    simpa [prefixWord, tailWord_406563, baseEnd_406563] using wordTrace_append hprefix tailTrace_406563
  have hstable : (prefixWord ++ tailWord_406563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406563).length < 2 ^ (prefixWord ++ tailWord_406563).sum := by decide
  have hdescent : baseEnd_406563 < baseStart_406563 := by decide
  rcases family_descends (prefixWord ++ tailWord_406563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406579 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3]
def baseStart_406579 : Nat := 118140960795 + 406579 * 2 ^ 59
def prefixEnd_406579 : Nat := 4983230072969 + 3 ^ 40 * 406579 * 2
def baseEnd_406579 : Nat := 208770451024469991492683

theorem tailTrace_406579 : CollatzResearch.WordTrace tailWord_406579 prefixEnd_406579 208770451024469991492683 := by
  unfold tailWord_406579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829154394041196010054791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886102929360797340036527 14829154394041196010054791)
  ·
    refine ⟨22243731591061794015082187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14829154394041196010054791 22243731591061794015082187)
    ·
      refine ⟨33365597386592691022623281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22243731591061794015082187 33365597386592691022623281)
      ·
        refine ⟨25024198039944518266967461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33365597386592691022623281 25024198039944518266967461)
        ·
          refine ⟨4692037132489597175056399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25024198039944518266967461 4692037132489597175056399)
          ·
            refine ⟨7038055698734395762584599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4692037132489597175056399 7038055698734395762584599)
            ·
              refine ⟨10557083548101593643876899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7038055698734395762584599 10557083548101593643876899)
              ·
                refine ⟨15835625322152390465815349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10557083548101593643876899 15835625322152390465815349)
                ·
                  refine ⟨1484589873951786606170189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15835625322152390465815349 1484589873951786606170189)
                  ·
                    refine ⟨556721202731919977313821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1484589873951786606170189 556721202731919977313821)
                    ·
                      refine ⟨208770451024469991492683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 556721202731919977313821 208770451024469991492683)
                      ·
                        rfl

theorem cell23_406579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 3].length) (baseStart_406579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406579 prefixEnd_406579 := by exact prefixLift 406579
  have htrace : WordTrace (prefixWord ++ tailWord_406579) baseStart_406579 baseEnd_406579 := by
    simpa [prefixWord, tailWord_406579, baseEnd_406579] using wordTrace_append hprefix tailTrace_406579
  have hstable : (prefixWord ++ tailWord_406579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406579).length < 2 ^ (prefixWord ++ tailWord_406579).sum := by decide
  have hdescent : baseEnd_406579 < baseStart_406579 := by decide
  rcases family_descends (prefixWord ++ tailWord_406579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406593 : List Nat := [1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_406593 : Nat := 118140960795 + 406593 * 2 ^ 59
def prefixEnd_406593 : Nat := 4983230072969 + 3 ^ 40 * 406593 * 2
def baseEnd_406593 : Nat := 208777639753632936717619

theorem tailTrace_406593 : CollatzResearch.WordTrace tailWord_406593 prefixEnd_406593 208777639753632936717619 := by
  unfold tailWord_406593
  simp only [CollatzResearch.WordTrace]
  refine ⟨14829665015990476401064433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9886443343993650934042955 14829665015990476401064433)
  ·
    refine ⟨11122248761992857300798325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14829665015990476401064433 11122248761992857300798325)
    ·
      refine ⟨1042710821436830371949843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11122248761992857300798325 1042710821436830371949843)
      ·
        refine ⟨1564066232155245557924765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042710821436830371949843 1564066232155245557924765)
        ·
          refine ⟨586524837058217084221787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1564066232155245557924765 586524837058217084221787)
          ·
            refine ⟨879787255587325626332681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586524837058217084221787 879787255587325626332681)
            ·
              refine ⟨659840441690494219749511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879787255587325626332681 659840441690494219749511)
              ·
                refine ⟨989760662535741329624267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659840441690494219749511 989760662535741329624267)
                ·
                  refine ⟨1484640993803611994436401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 989760662535741329624267 1484640993803611994436401)
                  ·
                    refine ⟨1113480745352708995827301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1484640993803611994436401 1113480745352708995827301)
                    ·
                      refine ⟨208777639753632936717619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1113480745352708995827301 208777639753632936717619)
                      ·
                        rfl

theorem cell23_406593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_406593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406593 prefixEnd_406593 := by exact prefixLift 406593
  have htrace : WordTrace (prefixWord ++ tailWord_406593) baseStart_406593 baseEnd_406593 := by
    simpa [prefixWord, tailWord_406593, baseEnd_406593] using wordTrace_append hprefix tailTrace_406593
  have hstable : (prefixWord ++ tailWord_406593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406593).length < 2 ^ (prefixWord ++ tailWord_406593).sum := by decide
  have hdescent : baseEnd_406593 < baseStart_406593 := by decide
  rcases family_descends (prefixWord ++ tailWord_406593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406614 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 1, 1, 4]
def baseStart_406614 : Nat := 118140960795 + 406614 * 2 ^ 59
def prefixEnd_406614 : Nat := 4983230072969 + 3 ^ 40 * 406614 * 2
def baseEnd_406614 : Nat := 208788422847377354555023

theorem tailTrace_406614 : CollatzResearch.WordTrace tailWord_406614 prefixEnd_406614 208788422847377354555023 := by
  unfold tailWord_406614
  simp only [CollatzResearch.WordTrace]
  refine ⟨926901934307149811723681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9886953965942931325052597 926901934307149811723681)
  ·
    refine ⟨695176450730362358792761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 926901934307149811723681 695176450730362358792761)
    ·
      refine ⟨521382338047771769094571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 695176450730362358792761 521382338047771769094571)
      ·
        refine ⟨782073507071657653641857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521382338047771769094571 782073507071657653641857)
        ·
          refine ⟨586555130303743240231393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 782073507071657653641857 586555130303743240231393)
          ·
            refine ⟨439916347727807430173545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586555130303743240231393 439916347727807430173545)
            ·
              refine ⟨329937260795855572630159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439916347727807430173545 329937260795855572630159)
              ·
                refine ⟨494905891193783358945239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329937260795855572630159 494905891193783358945239)
                ·
                  refine ⟨742358836790675038417859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494905891193783358945239 742358836790675038417859)
                  ·
                    refine ⟨1113538255186012557626789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 742358836790675038417859 1113538255186012557626789)
                    ·
                      refine ⟨208788422847377354555023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1113538255186012557626789 208788422847377354555023)
                      ·
                        rfl

theorem cell23_406614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_406614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406614 prefixEnd_406614 := by exact prefixLift 406614
  have htrace : WordTrace (prefixWord ++ tailWord_406614) baseStart_406614 baseEnd_406614 := by
    simpa [prefixWord, tailWord_406614, baseEnd_406614] using wordTrace_append hprefix tailTrace_406614
  have hstable : (prefixWord ++ tailWord_406614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406614).length < 2 ^ (prefixWord ++ tailWord_406614).sum := by decide
  have hdescent : baseEnd_406614 < baseStart_406614 := by decide
  rcases family_descends (prefixWord ++ tailWord_406614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406623 : List Nat := [1, 1, 2, 3, 1, 1, 5, 3, 1, 3, 2]
def baseStart_406623 : Nat := 118140960795 + 406623 * 2 ^ 59
def prefixEnd_406623 : Nat := 4983230072969 + 3 ^ 40 * 406623 * 2
def baseEnd_406623 : Nat := 208793044173267819342481

theorem tailTrace_406623 : CollatzResearch.WordTrace tailWord_406623 prefixEnd_406623 208793044173267819342481 := by
  unfold tailWord_406623
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830759205881791524656523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9887172803921194349771015 14830759205881791524656523)
  ·
    refine ⟨22246138808822687286984785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14830759205881791524656523 22246138808822687286984785)
    ·
      refine ⟨16684604106617015465238589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22246138808822687286984785 16684604106617015465238589)
      ·
        refine ⟨6256726539981380799464471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16684604106617015465238589 6256726539981380799464471)
        ·
          refine ⟨9385089809972071199196707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256726539981380799464471 9385089809972071199196707)
          ·
            refine ⟨14077634714958106798795061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9385089809972071199196707 14077634714958106798795061)
            ·
              refine ⟨1319778254527322512387037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14077634714958106798795061 1319778254527322512387037)
              ·
                refine ⟨494916845447745942145139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1319778254527322512387037 494916845447745942145139)
                ·
                  refine ⟨742375268171618913217709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 494916845447745942145139 742375268171618913217709)
                  ·
                    refine ⟨278390725564357092456641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 742375268171618913217709 278390725564357092456641)
                    ·
                      refine ⟨208793044173267819342481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278390725564357092456641 208793044173267819342481)
                      ·
                        rfl

theorem cell23_406623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_406623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406623 prefixEnd_406623 := by exact prefixLift 406623
  have htrace : WordTrace (prefixWord ++ tailWord_406623) baseStart_406623 baseEnd_406623 := by
    simpa [prefixWord, tailWord_406623, baseEnd_406623] using wordTrace_append hprefix tailTrace_406623
  have hstable : (prefixWord ++ tailWord_406623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406623).length < 2 ^ (prefixWord ++ tailWord_406623).sum := by decide
  have hdescent : baseEnd_406623 < baseStart_406623 := by decide
  rcases family_descends (prefixWord ++ tailWord_406623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406629 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 4, 6]
def baseStart_406629 : Nat := 118140960795 + 406629 * 2 ^ 59
def prefixEnd_406629 : Nat := 4983230072969 + 3 ^ 40 * 406629 * 2
def baseEnd_406629 : Nat := 69598708352398265289151

theorem tailTrace_406629 : CollatzResearch.WordTrace tailWord_406629 prefixEnd_406629 69598708352398265289151 := by
  unfold tailWord_406629
  simp only [CollatzResearch.WordTrace]
  refine ⟨14830978043860054549374941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9887318695906703032916627 14830978043860054549374941)
  ·
    refine ⟨5561616766447520456015603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14830978043860054549374941 5561616766447520456015603)
    ·
      refine ⟨8342425149671280684023405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5561616766447520456015603 8342425149671280684023405)
      ·
        refine ⟨3128409431126730256508777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8342425149671280684023405 3128409431126730256508777)
        ·
          refine ⟨2346307073345047692381583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3128409431126730256508777 2346307073345047692381583)
          ·
            refine ⟨3519460610017571538572375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346307073345047692381583 3519460610017571538572375)
            ·
              refine ⟨5279190915026357307858563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519460610017571538572375 5279190915026357307858563)
              ·
                refine ⟨7918786372539535961787845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5279190915026357307858563 7918786372539535961787845)
                ·
                  refine ⟨1484772444851162992835221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7918786372539535961787845 1484772444851162992835221)
                  ·
                    refine ⟨69598708352398265289151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1484772444851162992835221 69598708352398265289151)
                    ·
                      rfl

theorem cell23_406629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 4, 6].length) (baseStart_406629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406629 prefixEnd_406629 := by exact prefixLift 406629
  have htrace : WordTrace (prefixWord ++ tailWord_406629) baseStart_406629 baseEnd_406629 := by
    simpa [prefixWord, tailWord_406629, baseEnd_406629] using wordTrace_append hprefix tailTrace_406629
  have hstable : (prefixWord ++ tailWord_406629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406629).length < 2 ^ (prefixWord ++ tailWord_406629).sum := by decide
  have hdescent : baseEnd_406629 < baseStart_406629 := by decide
  rcases family_descends (prefixWord ++ tailWord_406629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406646 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 2, 6]
def baseStart_406646 : Nat := 118140960795 + 406646 * 2 ^ 59
def prefixEnd_406646 : Nat := 4983230072969 + 3 ^ 40 * 406646 * 2
def baseEnd_406646 : Nat := 69601618076107076451625

theorem tailTrace_406646 : CollatzResearch.WordTrace tailWord_406646 prefixEnd_406646 69601618076107076451625 := by
  unfold tailWord_406646
  simp only [CollatzResearch.WordTrace]
  refine ⟨926974880299904153296487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9887732056532310968495861 926974880299904153296487)
  ·
    refine ⟨1390462320449856229944731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926974880299904153296487 1390462320449856229944731)
    ·
      refine ⟨2085693480674784344917097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1390462320449856229944731 2085693480674784344917097)
      ·
        refine ⟨1564270110506088258687823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085693480674784344917097 1564270110506088258687823)
        ·
          refine ⟨2346405165759132388031735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564270110506088258687823 2346405165759132388031735)
          ·
            refine ⟨3519607748638698582047603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2346405165759132388031735 3519607748638698582047603)
            ·
              refine ⟨5279411622958047873071405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519607748638698582047603 5279411622958047873071405)
              ·
                refine ⟨1979779358609267952401777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5279411622958047873071405 1979779358609267952401777)
                ·
                  refine ⟨1484834518956950964301333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979779358609267952401777 1484834518956950964301333)
                  ·
                    refine ⟨69601618076107076451625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1484834518956950964301333 69601618076107076451625)
                    ·
                      rfl

theorem cell23_406646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 2, 6].length) (baseStart_406646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406646 prefixEnd_406646 := by exact prefixLift 406646
  have htrace : WordTrace (prefixWord ++ tailWord_406646) baseStart_406646 baseEnd_406646 := by
    simpa [prefixWord, tailWord_406646, baseEnd_406646] using wordTrace_append hprefix tailTrace_406646
  have hstable : (prefixWord ++ tailWord_406646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406646).length < 2 ^ (prefixWord ++ tailWord_406646).sum := by decide
  have hdescent : baseEnd_406646 < baseStart_406646 := by decide
  rcases family_descends (prefixWord ++ tailWord_406646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406654 : List Nat := [4, 2, 4, 1, 2, 1, 2, 7]
def baseStart_406654 : Nat := 118140960795 + 406654 * 2 ^ 59
def prefixEnd_406654 : Nat := 4983230072969 + 3 ^ 40 * 406654 * 2
def baseEnd_406654 : Nat := 7733665261983599927957

theorem tailTrace_406654 : CollatzResearch.WordTrace tailWord_406654 prefixEnd_406654 7733665261983599927957 := by
  unfold tailWord_406654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853986233596185477379377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9887926579179655879356677 1853986233596185477379377)
  ·
    refine ⟨1390489675197139108034533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1853986233596185477379377 1390489675197139108034533)
    ·
      refine ⟨260716814099463582756475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1390489675197139108034533 260716814099463582756475)
      ·
        refine ⟨391075221149195374134713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260716814099463582756475 391075221149195374134713)
        ·
          refine ⟨293306415861896530601035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391075221149195374134713 293306415861896530601035)
          ·
            refine ⟨439959623792844795901553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293306415861896530601035 439959623792844795901553)
            ·
              refine ⟨329969717844633596926165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439959623792844795901553 329969717844633596926165)
              ·
                refine ⟨7733665261983599927957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 329969717844633596926165 7733665261983599927957)
                ·
                  rfl

theorem cell23_406654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_406654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406654 prefixEnd_406654 := by exact prefixLift 406654
  have htrace : WordTrace (prefixWord ++ tailWord_406654) baseStart_406654 baseEnd_406654 := by
    simpa [prefixWord, tailWord_406654, baseEnd_406654] using wordTrace_append hprefix tailTrace_406654
  have hstable : (prefixWord ++ tailWord_406654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406654).length < 2 ^ (prefixWord ++ tailWord_406654).sum := by decide
  have hdescent : baseEnd_406654 < baseStart_406654 := by decide
  rcases family_descends (prefixWord ++ tailWord_406654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406659 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 7]
def baseStart_406659 : Nat := 118140960795 + 406659 * 2 ^ 59
def prefixEnd_406659 : Nat := 4983230072969 + 3 ^ 40 * 406659 * 2
def baseEnd_406659 : Nat := 23201281052981075388035

theorem tailTrace_406659 : CollatzResearch.WordTrace tailWord_406659 prefixEnd_406659 23201281052981075388035 := by
  unfold tailWord_406659
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832072233751369672967031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9888048155834246448644687 14832072233751369672967031)
  ·
    refine ⟨22248108350627054509450547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14832072233751369672967031 22248108350627054509450547)
    ·
      refine ⟨33372162525940581764175821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22248108350627054509450547 33372162525940581764175821)
      ·
        refine ⟨12514560947227718161565933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33372162525940581764175821 12514560947227718161565933)
        ·
          refine ⟨4692960355210394310587225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12514560947227718161565933 4692960355210394310587225)
          ·
            refine ⟨3519720266407795732940419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4692960355210394310587225 3519720266407795732940419)
            ·
              refine ⟨5279580399611693599410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3519720266407795732940419 5279580399611693599410629)
              ·
                refine ⟨989921324927192549889493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5279580399611693599410629 989921324927192549889493)
                ·
                  refine ⟨23201281052981075388035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 989921324927192549889493 23201281052981075388035)
                  ·
                    rfl

theorem cell23_406659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 7].length) (baseStart_406659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406659 prefixEnd_406659 := by exact prefixLift 406659
  have htrace : WordTrace (prefixWord ++ tailWord_406659) baseStart_406659 baseEnd_406659 := by
    simpa [prefixWord, tailWord_406659, baseEnd_406659] using wordTrace_append hprefix tailTrace_406659
  have hstable : (prefixWord ++ tailWord_406659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406659).length < 2 ^ (prefixWord ++ tailWord_406659).sum := by decide
  have hdescent : baseEnd_406659 < baseStart_406659 := by decide
  rcases family_descends (prefixWord ++ tailWord_406659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406670 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_406670 : Nat := 118140960795 + 406670 * 2 ^ 59
def prefixEnd_406670 : Nat := 4983230072969 + 3 ^ 40 * 406670 * 2
def baseEnd_406670 : Nat := 208817177764029135454765

theorem tailTrace_406670 : CollatzResearch.WordTrace tailWord_406670 prefixEnd_406670 208817177764029135454765 := by
  unfold tailWord_406670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854059179588939818952183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9888315624474345701078309 1854059179588939818952183)
  ·
    refine ⟨2781088769383409728428275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1854059179588939818952183 2781088769383409728428275)
    ·
      refine ⟨4171633154075114592642413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781088769383409728428275 4171633154075114592642413)
      ·
        refine ⟨1564362432778167972240905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4171633154075114592642413 1564362432778167972240905)
        ·
          refine ⟨1173271824583625979180679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1564362432778167972240905 1173271824583625979180679)
          ·
            refine ⟨1759907736875438968771019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173271824583625979180679 1759907736875438968771019)
            ·
              refine ⟨2639861605313158453156529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1759907736875438968771019 2639861605313158453156529)
              ·
                refine ⟨1979896203984868839867397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2639861605313158453156529 1979896203984868839867397)
                ·
                  refine ⟨371230538247162907475137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1979896203984868839867397 371230538247162907475137)
                  ·
                    refine ⟨278422903685372180606353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 371230538247162907475137 278422903685372180606353)
                    ·
                      refine ⟨208817177764029135454765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278422903685372180606353 208817177764029135454765)
                      ·
                        rfl

theorem cell23_406670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_406670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406670 prefixEnd_406670 := by exact prefixLift 406670
  have htrace : WordTrace (prefixWord ++ tailWord_406670) baseStart_406670 baseEnd_406670 := by
    simpa [prefixWord, tailWord_406670, baseEnd_406670] using wordTrace_append hprefix tailTrace_406670
  have hstable : (prefixWord ++ tailWord_406670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406670).length < 2 ^ (prefixWord ++ tailWord_406670).sum := by decide
  have hdescent : baseEnd_406670 < baseStart_406670 := by decide
  rcases family_descends (prefixWord ++ tailWord_406670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406719 : List Nat := [1, 1, 2, 2, 2, 2, 2, 1, 2, 8]
def baseStart_406719 : Nat := 118140960795 + 406719 * 2 ^ 59
def prefixEnd_406719 : Nat := 4983230072969 + 3 ^ 40 * 406719 * 2
def baseEnd_406719 : Nat := 69614112772033147914013

theorem tailTrace_406719 : CollatzResearch.WordTrace tailWord_406719 prefixEnd_406719 69614112772033147914013 := by
  unfold tailWord_406719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834260613533999920151211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9889507075689333280100807 14834260613533999920151211)
  ·
    refine ⟨22251390920300999880226817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14834260613533999920151211 22251390920300999880226817)
    ·
      refine ⟨16688543190225749910170113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22251390920300999880226817 16688543190225749910170113)
      ·
        refine ⟨12516407392669312432627585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16688543190225749910170113 12516407392669312432627585)
        ·
          refine ⟨9387305544501984324470689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12516407392669312432627585 9387305544501984324470689)
          ·
            refine ⟨7040479158376488243353017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9387305544501984324470689 7040479158376488243353017)
            ·
              refine ⟨5280359368782366182514763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7040479158376488243353017 5280359368782366182514763)
              ·
                refine ⟨7920539053173549273772145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5280359368782366182514763 7920539053173549273772145)
                ·
                  refine ⟨5940404289880161955329109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7920539053173549273772145 5940404289880161955329109)
                  ·
                    refine ⟨69614112772033147914013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5940404289880161955329109 69614112772033147914013)
                    ·
                      rfl

theorem cell23_406719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 2, 8].length) (baseStart_406719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406719 prefixEnd_406719 := by exact prefixLift 406719
  have htrace : WordTrace (prefixWord ++ tailWord_406719) baseStart_406719 baseEnd_406719 := by
    simpa [prefixWord, tailWord_406719, baseEnd_406719] using wordTrace_append hprefix tailTrace_406719
  have hstable : (prefixWord ++ tailWord_406719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406719).length < 2 ^ (prefixWord ++ tailWord_406719).sum := by decide
  have hdescent : baseEnd_406719 < baseStart_406719 := by decide
  rcases family_descends (prefixWord ++ tailWord_406719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406739 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6]
def baseStart_406739 : Nat := 118140960795 + 406739 * 2 ^ 59
def prefixEnd_406739 : Nat := 4983230072969 + 3 ^ 40 * 406739 * 2
def baseEnd_406739 : Nat := 208852607929189365491947

theorem tailTrace_406739 : CollatzResearch.WordTrace tailWord_406739 prefixEnd_406739 208852607929189365491947 := by
  unfold tailWord_406739
  simp only [CollatzResearch.WordTrace]
  refine ⟨14834990073461543335879271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9889993382307695557252847 14834990073461543335879271)
  ·
    refine ⟨22252485110192315003818907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14834990073461543335879271 22252485110192315003818907)
    ·
      refine ⟨33378727665288472505728361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22252485110192315003818907 33378727665288472505728361)
      ·
        refine ⟨25034045748966354379296271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33378727665288472505728361 25034045748966354379296271)
        ·
          refine ⟨37551068623449531568944407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25034045748966354379296271 37551068623449531568944407)
          ·
            refine ⟨56326602935174297353416611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37551068623449531568944407 56326602935174297353416611)
            ·
              refine ⟨84489904402761446030124917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56326602935174297353416611 84489904402761446030124917)
              ·
                refine ⟨7920928537758885565324211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 84489904402761446030124917 7920928537758885565324211)
                ·
                  refine ⟨11881392806638328347986317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7920928537758885565324211 11881392806638328347986317)
                  ·
                    refine ⟨4455522302489373130494869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11881392806638328347986317 4455522302489373130494869)
                    ·
                      refine ⟨208852607929189365491947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4455522302489373130494869 208852607929189365491947)
                      ·
                        rfl

theorem cell23_406739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 6].length) (baseStart_406739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406739 prefixEnd_406739 := by exact prefixLift 406739
  have htrace : WordTrace (prefixWord ++ tailWord_406739) baseStart_406739 baseEnd_406739 := by
    simpa [prefixWord, tailWord_406739, baseEnd_406739] using wordTrace_append hprefix tailTrace_406739
  have hstable : (prefixWord ++ tailWord_406739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406739).length < 2 ^ (prefixWord ++ tailWord_406739).sum := by decide
  have hdescent : baseEnd_406739 < baseStart_406739 := by decide
  rcases family_descends (prefixWord ++ tailWord_406739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406746 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_406746 : Nat := 118140960795 + 406746 * 2 ^ 59
def prefixEnd_406746 : Nat := 4983230072969 + 3 ^ 40 * 406746 * 2
def baseEnd_406746 : Nat := 208856202293770838104415

theorem tailTrace_406746 : CollatzResearch.WordTrace tailWord_406746 prefixEnd_406746 208856202293770838104415 := by
  unfold tailWord_406746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708811346109045882846023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9890163589624122354256061 3708811346109045882846023)
  ·
    refine ⟨5563217019163568824269035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3708811346109045882846023 5563217019163568824269035)
    ·
      refine ⟨8344825528745353236403553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5563217019163568824269035 8344825528745353236403553)
      ·
        refine ⟨6258619146559014927302665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8344825528745353236403553 6258619146559014927302665)
        ·
          refine ⟨4693964359919261195476999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6258619146559014927302665 4693964359919261195476999)
          ·
            refine ⟨7040946539878891793215499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4693964359919261195476999 7040946539878891793215499)
            ·
              refine ⟨10561419809818337689823249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7040946539878891793215499 10561419809818337689823249)
              ·
                refine ⟨7921064857363753267367437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10561419809818337689823249 7921064857363753267367437)
                ·
                  refine ⟨2970399321511407475262789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7921064857363753267367437 2970399321511407475262789)
                  ·
                    refine ⟨556949872783388901611773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2970399321511407475262789 556949872783388901611773)
                    ·
                      refine ⟨208856202293770838104415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 556949872783388901611773 208856202293770838104415)
                      ·
                        rfl

theorem cell23_406746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_406746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406746 prefixEnd_406746 := by exact prefixLift 406746
  have htrace : WordTrace (prefixWord ++ tailWord_406746) baseStart_406746 baseEnd_406746 := by
    simpa [prefixWord, tailWord_406746, baseEnd_406746] using wordTrace_append hprefix tailTrace_406746
  have hstable : (prefixWord ++ tailWord_406746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406746).length < 2 ^ (prefixWord ++ tailWord_406746).sum := by decide
  have hdescent : baseEnd_406746 < baseStart_406746 := by decide
  rcases family_descends (prefixWord ++ tailWord_406746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406770 : List Nat := [3, 2, 1, 3, 3, 1, 1, 2, 3, 4]
def baseStart_406770 : Nat := 118140960795 + 406770 * 2 ^ 59
def prefixEnd_406770 : Nat := 4983230072969 + 3 ^ 40 * 406770 * 2
def baseEnd_406770 : Nat := 69622841943159581401435

theorem tailTrace_406770 : CollatzResearch.WordTrace tailWord_406770 prefixEnd_406770 69622841943159581401435 := by
  unfold tailWord_406770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709030184087308907564441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9890747157566157086838509 3709030184087308907564441)
  ·
    refine ⟨2781772638065481680673331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3709030184087308907564441 2781772638065481680673331)
    ·
      refine ⟨4172658957098222521009997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781772638065481680673331 4172658957098222521009997)
      ·
        refine ⟨1564747108911833445378749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4172658957098222521009997 1564747108911833445378749)
        ·
          refine ⟨586780165841937542017031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1564747108911833445378749 586780165841937542017031)
          ·
            refine ⟨880170248762906313025547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586780165841937542017031 880170248762906313025547)
            ·
              refine ⟨1320255373144359469538321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 880170248762906313025547 1320255373144359469538321)
              ·
                refine ⟨990191529858269602153741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1320255373144359469538321 990191529858269602153741)
                ·
                  refine ⟨371321823696851100807653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990191529858269602153741 371321823696851100807653)
                  ·
                    refine ⟨69622841943159581401435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371321823696851100807653 69622841943159581401435)
                    ·
                      rfl

theorem cell23_406770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_406770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406770 prefixEnd_406770 := by exact prefixLift 406770
  have htrace : WordTrace (prefixWord ++ tailWord_406770) baseStart_406770 baseEnd_406770 := by
    simpa [prefixWord, tailWord_406770, baseEnd_406770] using wordTrace_append hprefix tailTrace_406770
  have hstable : (prefixWord ++ tailWord_406770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406770).length < 2 ^ (prefixWord ++ tailWord_406770).sum := by decide
  have hdescent : baseEnd_406770 < baseStart_406770 := by decide
  rcases family_descends (prefixWord ++ tailWord_406770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406793 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 3]
def baseStart_406793 : Nat := 118140960795 + 406793 * 2 ^ 59
def prefixEnd_406793 : Nat := 4983230072969 + 3 ^ 40 * 406793 * 2
def baseEnd_406793 : Nat := 208880335884532154216699

theorem tailTrace_406793 : CollatzResearch.WordTrace tailWord_406793 prefixEnd_406793 208880335884532154216699 := by
  unfold tailWord_406793
  simp only [CollatzResearch.WordTrace]
  refine ⟨14836959615265910558345033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9891306410177273705563355 14836959615265910558345033)
  ·
    refine ⟨11127719711449432918758775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14836959615265910558345033 11127719711449432918758775)
    ·
      refine ⟨16691579567174149378138163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11127719711449432918758775 16691579567174149378138163)
      ·
        refine ⟨25037369350761224067207245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16691579567174149378138163 25037369350761224067207245)
        ·
          refine ⟨9389013506535459025202717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25037369350761224067207245 9389013506535459025202717)
          ·
            refine ⟨3520880064950797134451019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9389013506535459025202717 3520880064950797134451019)
            ·
              refine ⟨5281320097426195701676529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3520880064950797134451019 5281320097426195701676529)
              ·
                refine ⟨3960990073069646776257397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5281320097426195701676529 3960990073069646776257397)
                ·
                  refine ⟨371342819350279385274131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3960990073069646776257397 371342819350279385274131)
                  ·
                    refine ⟨557014229025419077911197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371342819350279385274131 557014229025419077911197)
                    ·
                      refine ⟨208880335884532154216699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557014229025419077911197 208880335884532154216699)
                      ·
                        rfl

theorem cell23_406793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 1, 3].length) (baseStart_406793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406793 prefixEnd_406793 := by exact prefixLift 406793
  have htrace : WordTrace (prefixWord ++ tailWord_406793) baseStart_406793 baseEnd_406793 := by
    simpa [prefixWord, tailWord_406793, baseEnd_406793] using wordTrace_append hprefix tailTrace_406793
  have hstable : (prefixWord ++ tailWord_406793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406793).length < 2 ^ (prefixWord ++ tailWord_406793).sum := by decide
  have hdescent : baseEnd_406793 < baseStart_406793 := by decide
  rcases family_descends (prefixWord ++ tailWord_406793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406810 : List Nat := [3, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_406810 : Nat := 118140960795 + 406810 * 2 ^ 59
def prefixEnd_406810 : Nat := 4983230072969 + 3 ^ 40 * 406810 * 2
def baseEnd_406810 : Nat := 208889065055658587704121

theorem tailTrace_406810 : CollatzResearch.WordTrace tailWord_406810 prefixEnd_406810 208889065055658587704121 := by
  unfold tailWord_406810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709394914051080615428471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9891719770802881641142589 3709394914051080615428471)
  ·
    refine ⟨5564092371076620923142707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3709394914051080615428471 5564092371076620923142707)
    ·
      refine ⟨8346138556614931384714061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5564092371076620923142707 8346138556614931384714061)
      ·
        refine ⟨3129801958730599269267773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8346138556614931384714061 3129801958730599269267773)
        ·
          refine ⟨1173675734523974725975415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3129801958730599269267773 1173675734523974725975415)
          ·
            refine ⟨1760513601785962088963123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173675734523974725975415 1760513601785962088963123)
            ·
              refine ⟨2640770402678943133444685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1760513601785962088963123 2640770402678943133444685)
              ·
                refine ⟨990288901004603675041757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2640770402678943133444685 990288901004603675041757)
                ·
                  refine ⟨371358337876726378140659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990288901004603675041757 371358337876726378140659)
                  ·
                    refine ⟨557037506815089567210989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371358337876726378140659 557037506815089567210989)
                    ·
                      refine ⟨208889065055658587704121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557037506815089567210989 208889065055658587704121)
                      ·
                        rfl

theorem cell23_406810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_406810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406810 prefixEnd_406810 := by exact prefixLift 406810
  have htrace : WordTrace (prefixWord ++ tailWord_406810) baseStart_406810 baseEnd_406810 := by
    simpa [prefixWord, tailWord_406810, baseEnd_406810] using wordTrace_append hprefix tailTrace_406810
  have hstable : (prefixWord ++ tailWord_406810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406810).length < 2 ^ (prefixWord ++ tailWord_406810).sum := by decide
  have hdescent : baseEnd_406810 < baseStart_406810 := by decide
  rcases family_descends (prefixWord ++ tailWord_406810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406838 : List Nat := [5, 1, 2, 3, 2, 1, 1, 3, 1, 4]
def baseStart_406838 : Nat := 118140960795 + 406838 * 2 ^ 59
def prefixEnd_406838 : Nat := 4983230072969 + 3 ^ 40 * 406838 * 2
def baseEnd_406838 : Nat := 69634480837994826051331

theorem tailTrace_406838 : CollatzResearch.WordTrace tailWord_406838 prefixEnd_406838 69634480837994826051331 := by
  unfold tailWord_406838
  simp only [CollatzResearch.WordTrace]
  refine ⟨927412556256430202733323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9892400600068588829155445 927412556256430202733323)
  ·
    refine ⟨1391118834384645304099985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 927412556256430202733323 1391118834384645304099985)
    ·
      refine ⟨1043339125788483978074989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1391118834384645304099985 1043339125788483978074989)
      ·
        refine ⟨391252172170681491778121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1043339125788483978074989 391252172170681491778121)
        ·
          refine ⟨293439129128011118833591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391252172170681491778121 293439129128011118833591)
          ·
            refine ⟨440158693692016678250387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293439129128011118833591 440158693692016678250387)
            ·
              refine ⟨660238040538025017375581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440158693692016678250387 660238040538025017375581)
              ·
                refine ⟨247589265201759381515843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660238040538025017375581 247589265201759381515843)
                ·
                  refine ⟨371383897802639072273765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247589265201759381515843 371383897802639072273765)
                  ·
                    refine ⟨69634480837994826051331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371383897802639072273765 69634480837994826051331)
                    ·
                      rfl

theorem cell23_406838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_406838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406838 prefixEnd_406838 := by exact prefixLift 406838
  have htrace : WordTrace (prefixWord ++ tailWord_406838) baseStart_406838 baseEnd_406838 := by
    simpa [prefixWord, tailWord_406838, baseEnd_406838] using wordTrace_append hprefix tailTrace_406838
  have hstable : (prefixWord ++ tailWord_406838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406838).length < 2 ^ (prefixWord ++ tailWord_406838).sum := by decide
  have hdescent : baseEnd_406838 < baseStart_406838 := by decide
  rcases family_descends (prefixWord ++ tailWord_406838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406844 : List Nat := [2, 2, 2, 2, 1, 5, 1, 3, 1, 1, 3]
def baseStart_406844 : Nat := 118140960795 + 406844 * 2 ^ 59
def prefixEnd_406844 : Nat := 4983230072969 + 3 ^ 40 * 406844 * 2
def baseEnd_406844 : Nat := 208906523397911454678965

theorem tailTrace_406844 : CollatzResearch.WordTrace tailWord_406844 prefixEnd_406844 208906523397911454678965 := by
  unfold tailWord_406844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7419409869040573134225793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9892546492054097512301057 7419409869040573134225793)
  ·
    refine ⟨5564557401780429850669345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7419409869040573134225793 5564557401780429850669345)
    ·
      refine ⟨4173418051335322388002009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5564557401780429850669345 4173418051335322388002009)
      ·
        refine ⟨3130063538501491791001507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4173418051335322388002009 3130063538501491791001507)
        ·
          refine ⟨4695095307752237686502261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130063538501491791001507 4695095307752237686502261)
          ·
            refine ⟨440165185101772283109587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4695095307752237686502261 440165185101772283109587)
            ·
              refine ⟨660247777652658424664381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440165185101772283109587 660247777652658424664381)
              ·
                refine ⟨247592916619746909249143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 660247777652658424664381 247592916619746909249143)
                ·
                  refine ⟨371389374929620363873715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247592916619746909249143 371389374929620363873715)
                  ·
                    refine ⟨557084062394430545810573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371389374929620363873715 557084062394430545810573)
                    ·
                      refine ⟨208906523397911454678965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557084062394430545810573 208906523397911454678965)
                      ·
                        rfl

theorem cell23_406844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 3, 1, 1, 3].length) (baseStart_406844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406844 prefixEnd_406844 := by exact prefixLift 406844
  have htrace : WordTrace (prefixWord ++ tailWord_406844) baseStart_406844 baseEnd_406844 := by
    simpa [prefixWord, tailWord_406844, baseEnd_406844] using wordTrace_append hprefix tailTrace_406844
  have hstable : (prefixWord ++ tailWord_406844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406844).length < 2 ^ (prefixWord ++ tailWord_406844).sum := by decide
  have hdescent : baseEnd_406844 < baseStart_406844 := by decide
  rcases family_descends (prefixWord ++ tailWord_406844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406861 : List Nat := [1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_406861 : Nat := 118140960795 + 406861 * 2 ^ 59
def prefixEnd_406861 : Nat := 4983230072969 + 3 ^ 40 * 406861 * 2
def baseEnd_406861 : Nat := 208915252569037888166387

theorem tailTrace_406861 : CollatzResearch.WordTrace tailWord_406861 prefixEnd_406861 208915252569037888166387 := by
  unfold tailWord_406861
  simp only [CollatzResearch.WordTrace]
  refine ⟨14839439779019558171820437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9892959852679705447880291 14839439779019558171820437)
  ·
    refine ⟨695598739641541789304083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14839439779019558171820437 695598739641541789304083)
    ·
      refine ⟨1043398109462312683956125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695598739641541789304083 1043398109462312683956125)
      ·
        refine ⟨391274291048367256483547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1043398109462312683956125 391274291048367256483547)
        ·
          refine ⟨586911436572550884725321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391274291048367256483547 586911436572550884725321)
          ·
            refine ⟨440183577429413163543991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586911436572550884725321 440183577429413163543991)
            ·
              refine ⟨660275366144119745315987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440183577429413163543991 660275366144119745315987)
              ·
                refine ⟨990413049216179617973981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 660275366144119745315987 990413049216179617973981)
                ·
                  refine ⟨371404893456067356740243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 990413049216179617973981 371404893456067356740243)
                  ·
                    refine ⟨557107340184101035110365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371404893456067356740243 557107340184101035110365)
                    ·
                      refine ⟨208915252569037888166387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557107340184101035110365 208915252569037888166387)
                      ·
                        rfl

theorem cell23_406861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_406861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406861 prefixEnd_406861 := by exact prefixLift 406861
  have htrace : WordTrace (prefixWord ++ tailWord_406861) baseStart_406861 baseEnd_406861 := by
    simpa [prefixWord, tailWord_406861, baseEnd_406861] using wordTrace_append hprefix tailTrace_406861
  have hstable : (prefixWord ++ tailWord_406861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406861).length < 2 ^ (prefixWord ++ tailWord_406861).sum := by decide
  have hdescent : baseEnd_406861 < baseStart_406861 := by decide
  rcases family_descends (prefixWord ++ tailWord_406861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406906 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_406906 : Nat := 118140960795 + 406906 * 2 ^ 59
def prefixEnd_406906 : Nat := 4983230072969 + 3 ^ 40 * 406906 * 2
def baseEnd_406906 : Nat := 208938359198490212103679

theorem tailTrace_406906 : CollatzResearch.WordTrace tailWord_406906 prefixEnd_406906 208938359198490212103679 := by
  unfold tailWord_406906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710270265964132714302143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9894054042571020571472381 3710270265964132714302143)
  ·
    refine ⟨5565405398946199071453215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3710270265964132714302143 5565405398946199071453215)
    ·
      refine ⟨8348108098419298607179823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5565405398946199071453215 8348108098419298607179823)
      ·
        refine ⟨12522162147628947910769735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8348108098419298607179823 12522162147628947910769735)
        ·
          refine ⟨18783243221443421866154603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12522162147628947910769735 18783243221443421866154603)
          ·
            refine ⟨28174864832165132799231905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18783243221443421866154603 28174864832165132799231905)
            ·
              refine ⟨21131148624123849599423929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28174864832165132799231905 21131148624123849599423929)
              ·
                refine ⟨15848361468092887199567947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21131148624123849599423929 15848361468092887199567947)
                ·
                  refine ⟨23772542202139330799351921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15848361468092887199567947 23772542202139330799351921)
                  ·
                    refine ⟨17829406651604498099513941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23772542202139330799351921 17829406651604498099513941)
                    ·
                      refine ⟨208938359198490212103679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 17829406651604498099513941 208938359198490212103679)
                      ·
                        rfl

theorem cell23_406906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_406906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406906 prefixEnd_406906 := by exact prefixLift 406906
  have htrace : WordTrace (prefixWord ++ tailWord_406906) baseStart_406906 baseEnd_406906 := by
    simpa [prefixWord, tailWord_406906, baseEnd_406906] using wordTrace_append hprefix tailTrace_406906
  have hstable : (prefixWord ++ tailWord_406906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406906).length < 2 ^ (prefixWord ++ tailWord_406906).sum := by decide
  have hdescent : baseEnd_406906 < baseStart_406906 := by decide
  rcases family_descends (prefixWord ++ tailWord_406906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406980 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 7]
def baseStart_406980 : Nat := 118140960795 + 406980 * 2 ^ 59
def prefixEnd_406980 : Nat := 4983230072969 + 3 ^ 40 * 406980 * 2
def baseEnd_406980 : Nat := 23219595196324769175371

theorem tailTrace_406980 : CollatzResearch.WordTrace tailWord_406980 prefixEnd_406980 23219595196324769175371 := by
  unfold tailWord_406980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7421890032794220747701197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9895853377058960996934929 7421890032794220747701197)
  ·
    refine ⟨2783208762297832780387949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7421890032794220747701197 2783208762297832780387949)
    ·
      refine ⟨1043703285861687292645481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2783208762297832780387949 1043703285861687292645481)
      ·
        refine ⟨782777464396265469484111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1043703285861687292645481 782777464396265469484111)
        ·
          refine ⟨1174166196594398204226167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782777464396265469484111 1174166196594398204226167)
          ·
            refine ⟨1761249294891597306339251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174166196594398204226167 1761249294891597306339251)
            ·
              refine ⟨2641873942337395959508877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1761249294891597306339251 2641873942337395959508877)
              ·
                refine ⟨990702728376523484815829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2641873942337395959508877 990702728376523484815829)
                ·
                  refine ⟨23219595196324769175371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 990702728376523484815829 23219595196324769175371)
                  ·
                    rfl

theorem cell23_406980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_406980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406980 prefixEnd_406980 := by exact prefixLift 406980
  have htrace : WordTrace (prefixWord ++ tailWord_406980) baseStart_406980 baseEnd_406980 := by
    simpa [prefixWord, tailWord_406980, baseEnd_406980] using wordTrace_append hprefix tailTrace_406980
  have hstable : (prefixWord ++ tailWord_406980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406980).length < 2 ^ (prefixWord ++ tailWord_406980).sum := by decide
  have hdescent : baseEnd_406980 < baseStart_406980 := by decide
  rcases family_descends (prefixWord ++ tailWord_406980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406990 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_406990 : Nat := 118140960795 + 406990 * 2 ^ 59
def prefixEnd_406990 : Nat := 4983230072969 + 3 ^ 40 * 406990 * 2
def baseEnd_406990 : Nat := 208981491573467883453293

theorem tailTrace_406990 : CollatzResearch.WordTrace tailWord_406990 prefixEnd_406990 208981491573467883453293 := by
  unfold tailWord_406990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855518099444026650408303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9896096530368142135510949 1855518099444026650408303)
  ·
    refine ⟨2783277149166039975612455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1855518099444026650408303 2783277149166039975612455)
    ·
      refine ⟨4174915723749059963418683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783277149166039975612455 4174915723749059963418683)
      ·
        refine ⟨6262373585623589945128025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4174915723749059963418683 6262373585623589945128025)
        ·
          refine ⟨4696780189217692458846019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262373585623589945128025 4696780189217692458846019)
          ·
            refine ⟨7045170283826538688269029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696780189217692458846019 7045170283826538688269029)
            ·
              refine ⟨1320969428217476004050443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7045170283826538688269029 1320969428217476004050443)
              ·
                refine ⟨1981454142326214006075665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1320969428217476004050443 1981454142326214006075665)
                ·
                  refine ⟨1486090606744660504556749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1981454142326214006075665 1486090606744660504556749)
                  ·
                    refine ⟨557283977529247689208781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486090606744660504556749 557283977529247689208781)
                    ·
                      refine ⟨208981491573467883453293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557283977529247689208781 208981491573467883453293)
                      ·
                        rfl

theorem cell23_406990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_406990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_406990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_406990 prefixEnd_406990 := by exact prefixLift 406990
  have htrace : WordTrace (prefixWord ++ tailWord_406990) baseStart_406990 baseEnd_406990 := by
    simpa [prefixWord, tailWord_406990, baseEnd_406990] using wordTrace_append hprefix tailTrace_406990
  have hstable : (prefixWord ++ tailWord_406990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406990).length < 2 ^ (prefixWord ++ tailWord_406990).sum := by decide
  have hdescent : baseEnd_406990 < baseStart_406990 := by decide
  rcases family_descends (prefixWord ++ tailWord_406990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407000 : List Nat := [2, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_407000 : Nat := 118140960795 + 407000 * 2 ^ 59
def prefixEnd_407000 : Nat := 4983230072969 + 3 ^ 40 * 407000 * 2
def baseEnd_407000 : Nat := 208986626380012844328247

theorem tailTrace_407000 : CollatzResearch.WordTrace tailWord_407000 prefixEnd_407000 208986626380012844328247 := by
  unfold tailWord_407000
  simp only [CollatzResearch.WordTrace]
  refine ⟨7422254762757992455565227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9896339683677323274086969 7422254762757992455565227)
  ·
    refine ⟨11133382144136988683347841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7422254762757992455565227 11133382144136988683347841)
    ·
      refine ⟨8350036608102741512510881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11133382144136988683347841 8350036608102741512510881)
      ·
        refine ⟨6262527456077056134383161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8350036608102741512510881 6262527456077056134383161)
        ·
          refine ⟨4696895592057792100787371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6262527456077056134383161 4696895592057792100787371)
          ·
            refine ⟨7045343388086688151181057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4696895592057792100787371 7045343388086688151181057)
            ·
              refine ⟨5284007541065016113385793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7045343388086688151181057 5284007541065016113385793)
              ·
                refine ⟨3963005655798762085039345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5284007541065016113385793 3963005655798762085039345)
                ·
                  refine ⟨2972254241849071563779509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3963005655798762085039345 2972254241849071563779509)
                  ·
                    refine ⟨278648835173350459104329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2972254241849071563779509 278648835173350459104329)
                    ·
                      refine ⟨208986626380012844328247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278648835173350459104329 208986626380012844328247)
                      ·
                        rfl

theorem cell23_407000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_407000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407000 prefixEnd_407000 := by exact prefixLift 407000
  have htrace : WordTrace (prefixWord ++ tailWord_407000) baseStart_407000 baseEnd_407000 := by
    simpa [prefixWord, tailWord_407000, baseEnd_407000] using wordTrace_append hprefix tailTrace_407000
  have hstable : (prefixWord ++ tailWord_407000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407000).length < 2 ^ (prefixWord ++ tailWord_407000).sum := by decide
  have hdescent : baseEnd_407000 < baseStart_407000 := by decide
  rcases family_descends (prefixWord ++ tailWord_407000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407043 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4]
def baseStart_407043 : Nat := 118140960795 + 407043 * 2 ^ 59
def prefixEnd_407043 : Nat := 4983230072969 + 3 ^ 40 * 407043 * 2
def baseEnd_407043 : Nat := 209008706048156176090549

theorem tailTrace_407043 : CollatzResearch.WordTrace tailWord_407043 prefixEnd_407043 209008706048156176090549 := by
  unfold tailWord_407043
  simp only [CollatzResearch.WordTrace]
  refine ⟨14846077864360203254945783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9897385242906802169963855 14846077864360203254945783)
  ·
    refine ⟨22269116796540304882418675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14846077864360203254945783 22269116796540304882418675)
    ·
      refine ⟨33403675194810457323628013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22269116796540304882418675 33403675194810457323628013)
      ·
        refine ⟨12526378198053921496360505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33403675194810457323628013 12526378198053921496360505)
        ·
          refine ⟨9394783648540441122270379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12526378198053921496360505 9394783648540441122270379)
          ·
            refine ⟨14092175472810661683405569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9394783648540441122270379 14092175472810661683405569)
            ·
              refine ⟨10569131604607996262554177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14092175472810661683405569 10569131604607996262554177)
              ·
                refine ⟨7926848703455997196915633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10569131604607996262554177 7926848703455997196915633)
                ·
                  refine ⟨5945136527591997897686725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7926848703455997196915633 5945136527591997897686725)
                  ·
                    refine ⟨1114713098923499605816261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5945136527591997897686725 1114713098923499605816261)
                    ·
                      refine ⟨209008706048156176090549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1114713098923499605816261 209008706048156176090549)
                      ·
                        rfl

theorem cell23_407043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_407043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407043 prefixEnd_407043 := by exact prefixLift 407043
  have htrace : WordTrace (prefixWord ++ tailWord_407043) baseStart_407043 baseEnd_407043 := by
    simpa [prefixWord, tailWord_407043, baseEnd_407043] using wordTrace_append hprefix tailTrace_407043
  have hstable : (prefixWord ++ tailWord_407043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407043).length < 2 ^ (prefixWord ++ tailWord_407043).sum := by decide
  have hdescent : baseEnd_407043 < baseStart_407043 := by decide
  rcases family_descends (prefixWord ++ tailWord_407043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407091 : List Nat := [1, 1, 1, 2, 4, 5, 2, 2, 1, 4]
def baseStart_407091 : Nat := 118140960795 + 407091 * 2 ^ 59
def prefixEnd_407091 : Nat := 4983230072969 + 3 ^ 40 * 407091 * 2
def baseEnd_407091 : Nat := 69677784373190662763443

theorem tailTrace_407091 : CollatzResearch.WordTrace tailWord_407091 prefixEnd_407091 69677784373190662763443 := by
  unfold tailWord_407091
  simp only [CollatzResearch.WordTrace]
  refine ⟨14847828568186307452693127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9898552378790871635128751 14847828568186307452693127)
  ·
    refine ⟨22271742852279461179039691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14847828568186307452693127 22271742852279461179039691)
    ·
      refine ⟨33407614278419191768559537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22271742852279461179039691 33407614278419191768559537)
      ·
        refine ⟨25055710708814393826419653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33407614278419191768559537 25055710708814393826419653)
        ·
          refine ⟨4697945757902698842453685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25055710708814393826419653 4697945757902698842453685)
          ·
            refine ⟨440432414803378016480033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4697945757902698842453685 440432414803378016480033)
            ·
              refine ⟨330324311102533512360025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440432414803378016480033 330324311102533512360025)
              ·
                refine ⟨247743233326900134270019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330324311102533512360025 247743233326900134270019)
                ·
                  refine ⟨371614849990350201405029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247743233326900134270019 371614849990350201405029)
                  ·
                    refine ⟨69677784373190662763443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 371614849990350201405029 69677784373190662763443)
                    ·
                      rfl

theorem cell23_407091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 1, 4].length) (baseStart_407091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407091 prefixEnd_407091 := by exact prefixLift 407091
  have htrace : WordTrace (prefixWord ++ tailWord_407091) baseStart_407091 baseEnd_407091 := by
    simpa [prefixWord, tailWord_407091, baseEnd_407091] using wordTrace_append hprefix tailTrace_407091
  have hstable : (prefixWord ++ tailWord_407091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407091).length < 2 ^ (prefixWord ++ tailWord_407091).sum := by decide
  have hdescent : baseEnd_407091 < baseStart_407091 := by decide
  rcases family_descends (prefixWord ++ tailWord_407091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407120 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4]
def baseStart_407120 : Nat := 118140960795 + 407120 * 2 ^ 59
def prefixEnd_407120 : Nat := 4983230072969 + 3 ^ 40 * 407120 * 2
def baseEnd_407120 : Nat := 209048244058552374827695

theorem tailTrace_407120 : CollatzResearch.WordTrace tailWord_407120 prefixEnd_407120 209048244058552374827695 := by
  unfold tailWord_407120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424443142540622702749407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9899257523387496936999209 7424443142540622702749407)
  ·
    refine ⟨11136664713810934054124111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7424443142540622702749407 11136664713810934054124111)
    ·
      refine ⟨16704997070716401081186167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11136664713810934054124111 16704997070716401081186167)
      ·
        refine ⟨25057495606074601621779251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16704997070716401081186167 25057495606074601621779251)
        ·
          refine ⟨37586243409111902432668877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25057495606074601621779251 37586243409111902432668877)
          ·
            refine ⟨14094841278416963412250829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37586243409111902432668877 14094841278416963412250829)
            ·
              refine ⟨5285565479406361279594061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14094841278416963412250829 5285565479406361279594061)
              ·
                refine ⟨1982087054777385479847773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5285565479406361279594061 1982087054777385479847773)
                ·
                  refine ⟨743282645541519554942915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1982087054777385479847773 743282645541519554942915)
                  ·
                    refine ⟨1114923968312279332414373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 743282645541519554942915 1114923968312279332414373)
                    ·
                      refine ⟨209048244058552374827695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1114923968312279332414373 209048244058552374827695)
                      ·
                        rfl

theorem cell23_407120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_407120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407120 prefixEnd_407120 := by exact prefixLift 407120
  have htrace : WordTrace (prefixWord ++ tailWord_407120) baseStart_407120 baseEnd_407120 := by
    simpa [prefixWord, tailWord_407120, baseEnd_407120] using wordTrace_append hprefix tailTrace_407120
  have hstable : (prefixWord ++ tailWord_407120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407120).length < 2 ^ (prefixWord ++ tailWord_407120).sum := by decide
  have hdescent : baseEnd_407120 < baseStart_407120 := by decide
  rcases family_descends (prefixWord ++ tailWord_407120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407137 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_407137 : Nat := 118140960795 + 407137 * 2 ^ 59
def prefixEnd_407137 : Nat := 4983230072969 + 3 ^ 40 * 407137 * 2
def baseEnd_407137 : Nat := 209056973229678808315117

theorem tailTrace_407137 : CollatzResearch.WordTrace tailWord_407137 prefixEnd_407137 209056973229678808315117 := by
  unfold tailWord_407137
  simp only [CollatzResearch.WordTrace]
  refine ⟨14849506326019657308867665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9899670884013104872578443 14849506326019657308867665)
  ·
    refine ⟨11137129744514742981650749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14849506326019657308867665 11137129744514742981650749)
    ·
      refine ⟨4176423654193028618119031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11137129744514742981650749 4176423654193028618119031)
      ·
        refine ⟨6264635481289542927178547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4176423654193028618119031 6264635481289542927178547)
        ·
          refine ⟨9396953221934314390767821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6264635481289542927178547 9396953221934314390767821)
          ·
            refine ⟨3523857458225367896537933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9396953221934314390767821 3523857458225367896537933)
            ·
              refine ⟨1321446546834512961201725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3523857458225367896537933 1321446546834512961201725)
              ·
                refine ⟨495542455062942360450647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1321446546834512961201725 495542455062942360450647)
                ·
                  refine ⟨743313682594413540675971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 495542455062942360450647 743313682594413540675971)
                  ·
                    refine ⟨1114970523891620311013957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 743313682594413540675971 1114970523891620311013957)
                    ·
                      refine ⟨209056973229678808315117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1114970523891620311013957 209056973229678808315117)
                      ·
                        rfl

theorem cell23_407137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_407137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407137 prefixEnd_407137 := by exact prefixLift 407137
  have htrace : WordTrace (prefixWord ++ tailWord_407137) baseStart_407137 baseEnd_407137 := by
    simpa [prefixWord, tailWord_407137, baseEnd_407137] using wordTrace_append hprefix tailTrace_407137
  have hstable : (prefixWord ++ tailWord_407137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407137).length < 2 ^ (prefixWord ++ tailWord_407137).sum := by decide
  have hdescent : baseEnd_407137 < baseStart_407137 := by decide
  rcases family_descends (prefixWord ++ tailWord_407137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407157 : List Nat := [1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_407157 : Nat := 118140960795 + 407157 * 2 ^ 59
def prefixEnd_407157 : Nat := 4983230072969 + 3 ^ 40 * 407157 * 2
def baseEnd_407157 : Nat := 209067242842768730065025

theorem tailTrace_407157 : CollatzResearch.WordTrace tailWord_407157 prefixEnd_407157 209067242842768730065025 := by
  unfold tailWord_407157
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850235785947200724595725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9900157190631467149730483 14850235785947200724595725)
  ·
    refine ⟨5568838419730200271723397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14850235785947200724595725 5568838419730200271723397)
    ·
      refine ⟨1044157203699412550948137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5568838419730200271723397 1044157203699412550948137)
      ·
        refine ⟨783117902774559413211103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044157203699412550948137 783117902774559413211103)
        ·
          refine ⟨1174676854161839119816655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783117902774559413211103 1174676854161839119816655)
          ·
            refine ⟨1762015281242758679724983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174676854161839119816655 1762015281242758679724983)
            ·
              refine ⟨2643022921864138019587475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762015281242758679724983 2643022921864138019587475)
              ·
                refine ⟨3964534382796207029381213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2643022921864138019587475 3964534382796207029381213)
                ·
                  refine ⟨1486700393548577636017955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3964534382796207029381213 1486700393548577636017955)
                  ·
                    refine ⟨2230050590322866454026933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1486700393548577636017955 2230050590322866454026933)
                    ·
                      refine ⟨209067242842768730065025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2230050590322866454026933 209067242842768730065025)
                      ·
                        rfl

theorem cell23_407157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_407157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407157 prefixEnd_407157 := by exact prefixLift 407157
  have htrace : WordTrace (prefixWord ++ tailWord_407157) baseStart_407157 baseEnd_407157 := by
    simpa [prefixWord, tailWord_407157, baseEnd_407157] using wordTrace_append hprefix tailTrace_407157
  have hstable : (prefixWord ++ tailWord_407157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407157).length < 2 ^ (prefixWord ++ tailWord_407157).sum := by decide
  have hdescent : baseEnd_407157 < baseStart_407157 := by decide
  rcases family_descends (prefixWord ++ tailWord_407157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407204 : List Nat := [2, 3, 1, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_407204 : Nat := 118140960795 + 407204 * 2 ^ 59
def prefixEnd_407204 : Nat := 4983230072969 + 3 ^ 40 * 407204 * 2
def baseEnd_407204 : Nat := 209091376433530046177309

theorem tailTrace_407204 : CollatzResearch.WordTrace tailWord_407204 prefixEnd_407204 209091376433530046177309 := by
  unfold tailWord_407204
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425975008388463875778333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9901300011184618501037777 7425975008388463875778333)
  ·
    refine ⟨2784740628145673953416875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7425975008388463875778333 2784740628145673953416875)
    ·
      refine ⟨4177110942218510930125313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784740628145673953416875 4177110942218510930125313)
      ·
        refine ⟨3132833206663883197593985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4177110942218510930125313 3132833206663883197593985)
        ·
          refine ⟨2349624904997912398195489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3132833206663883197593985 2349624904997912398195489)
          ·
            refine ⟨1762218678748434298646617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2349624904997912398195489 1762218678748434298646617)
            ·
              refine ⟨1321664009061325723984963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762218678748434298646617 1321664009061325723984963)
              ·
                refine ⟨1982496013591988585977445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321664009061325723984963 1982496013591988585977445)
                ·
                  refine ⟨371718002548497859870771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982496013591988585977445 371718002548497859870771)
                  ·
                    refine ⟨557577003822746789806157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371718002548497859870771 557577003822746789806157)
                    ·
                      refine ⟨209091376433530046177309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557577003822746789806157 209091376433530046177309)
                      ·
                        rfl

theorem cell23_407204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_407204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407204 prefixEnd_407204 := by exact prefixLift 407204
  have htrace : WordTrace (prefixWord ++ tailWord_407204) baseStart_407204 baseEnd_407204 := by
    simpa [prefixWord, tailWord_407204, baseEnd_407204] using wordTrace_append hprefix tailTrace_407204
  have hstable : (prefixWord ++ tailWord_407204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407204).length < 2 ^ (prefixWord ++ tailWord_407204).sum := by decide
  have hdescent : baseEnd_407204 < baseStart_407204 := by decide
  rcases family_descends (prefixWord ++ tailWord_407204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407227 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 5, 4, 2]
def baseStart_407227 : Nat := 118140960795 + 407227 * 2 ^ 59
def prefixEnd_407227 : Nat := 4983230072969 + 3 ^ 40 * 407227 * 2
def baseEnd_407227 : Nat := 209103186488583456189703

theorem tailTrace_407227 : CollatzResearch.WordTrace tailWord_407227 prefixEnd_407227 209103186488583456189703 := by
  unfold tailWord_407227
  simp only [CollatzResearch.WordTrace]
  refine ⟨14852788895693602679643935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9901859263795735119762623 14852788895693602679643935)
  ·
    refine ⟨22279183343540404019465903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14852788895693602679643935 22279183343540404019465903)
    ·
      refine ⟨33418775015310606029198855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22279183343540404019465903 33418775015310606029198855)
      ·
        refine ⟨50128162522965909043798283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33418775015310606029198855 50128162522965909043798283)
        ·
          refine ⟨75192243784448863565697425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50128162522965909043798283 75192243784448863565697425)
          ·
            refine ⟨56394182838336647674273069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75192243784448863565697425 56394182838336647674273069)
            ·
              refine ⟨21147818564376242877852401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56394182838336647674273069 21147818564376242877852401)
              ·
                refine ⟨15860863923282182158389301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21147818564376242877852401 15860863923282182158389301)
                ·
                  refine ⟨1486955992807704577348997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15860863923282182158389301 1486955992807704577348997)
                  ·
                    refine ⟨278804248651444608252937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1486955992807704577348997 278804248651444608252937)
                    ·
                      refine ⟨209103186488583456189703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278804248651444608252937 209103186488583456189703)
                      ·
                        rfl

theorem cell23_407227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 5, 4, 2].length) (baseStart_407227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407227 prefixEnd_407227 := by exact prefixLift 407227
  have htrace : WordTrace (prefixWord ++ tailWord_407227) baseStart_407227 baseEnd_407227 := by
    simpa [prefixWord, tailWord_407227, baseEnd_407227] using wordTrace_append hprefix tailTrace_407227
  have hstable : (prefixWord ++ tailWord_407227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407227).length < 2 ^ (prefixWord ++ tailWord_407227).sum := by decide
  have hdescent : baseEnd_407227 < baseStart_407227 := by decide
  rcases family_descends (prefixWord ++ tailWord_407227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407238 : List Nat := [6, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_407238 : Nat := 118140960795 + 407238 * 2 ^ 59
def prefixEnd_407238 : Nat := 4983230072969 + 3 ^ 40 * 407238 * 2
def baseEnd_407238 : Nat := 209108834775782913152153

theorem tailTrace_407238 : CollatzResearch.WordTrace tailWord_407238 prefixEnd_407238 209108834775782913152153 := by
  unfold tailWord_407238
  simp only [CollatzResearch.WordTrace]
  refine ⟨464162190582929736196699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9902126732435834372196245 464162190582929736196699)
  ·
    refine ⟨696243285874394604295049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 464162190582929736196699 696243285874394604295049)
    ·
      refine ⟨522182464405795953221287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 696243285874394604295049 522182464405795953221287)
      ·
        refine ⟨783273696608693929831931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522182464405795953221287 783273696608693929831931)
        ·
          refine ⟨1174910544913040894747897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783273696608693929831931 1174910544913040894747897)
          ·
            refine ⟨881182908684780671060923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174910544913040894747897 881182908684780671060923)
            ·
              refine ⟨1321774363027171006591385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881182908684780671060923 1321774363027171006591385)
              ·
                refine ⟨991330772270378254943539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1321774363027171006591385 991330772270378254943539)
                ·
                  refine ⟨1486996158405567382415309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 991330772270378254943539 1486996158405567382415309)
                  ·
                    refine ⟨557623559402087768405741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1486996158405567382415309 557623559402087768405741)
                    ·
                      refine ⟨209108834775782913152153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557623559402087768405741 209108834775782913152153)
                      ·
                        rfl

theorem cell23_407238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_407238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407238 prefixEnd_407238 := by exact prefixLift 407238
  have htrace : WordTrace (prefixWord ++ tailWord_407238) baseStart_407238 baseEnd_407238 := by
    simpa [prefixWord, tailWord_407238, baseEnd_407238] using wordTrace_append hprefix tailTrace_407238
  have hstable : (prefixWord ++ tailWord_407238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407238).length < 2 ^ (prefixWord ++ tailWord_407238).sum := by decide
  have hdescent : baseEnd_407238 < baseStart_407238 := by decide
  rcases family_descends (prefixWord ++ tailWord_407238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407354 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_407354 : Nat := 118140960795 + 407354 * 2 ^ 59
def prefixEnd_407354 : Nat := 4983230072969 + 3 ^ 40 * 407354 * 2
def baseEnd_407354 : Nat := 209168398531704459301619

theorem tailTrace_407354 : CollatzResearch.WordTrace tailWord_407354 prefixEnd_407354 209168398531704459301619 := by
  unfold tailWord_407354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3714355241558375842379279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9904947310822335579678077 3714355241558375842379279)
  ·
    refine ⟨5571532862337563763568919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3714355241558375842379279 5571532862337563763568919)
    ·
      refine ⟨8357299293506345645353379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5571532862337563763568919 8357299293506345645353379)
      ·
        refine ⟨12535948940259518468030069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8357299293506345645353379 12535948940259518468030069)
        ·
          refine ⟨1175245213149329856377819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12535948940259518468030069 1175245213149329856377819)
          ·
            refine ⟨1762867819723994784566729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175245213149329856377819 1762867819723994784566729)
            ·
              refine ⟨1322150864792996088425047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1762867819723994784566729 1322150864792996088425047)
              ·
                refine ⟨1983226297189494132637571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322150864792996088425047 1983226297189494132637571)
                ·
                  refine ⟨2974839445784241198956357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1983226297189494132637571 2974839445784241198956357)
                  ·
                    refine ⟨557782396084545224804317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2974839445784241198956357 557782396084545224804317)
                    ·
                      refine ⟨209168398531704459301619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 557782396084545224804317 209168398531704459301619)
                      ·
                        rfl

theorem cell23_407354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_407354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407354 prefixEnd_407354 := by exact prefixLift 407354
  have htrace : WordTrace (prefixWord ++ tailWord_407354) baseStart_407354 baseEnd_407354 := by
    simpa [prefixWord, tailWord_407354, baseEnd_407354] using wordTrace_append hprefix tailTrace_407354
  have hstable : (prefixWord ++ tailWord_407354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407354).length < 2 ^ (prefixWord ++ tailWord_407354).sum := by decide
  have hdescent : baseEnd_407354 < baseStart_407354 := by decide
  rcases family_descends (prefixWord ++ tailWord_407354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407391 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 6]
def baseStart_407391 : Nat := 118140960795 + 407391 * 2 ^ 59
def prefixEnd_407391 : Nat := 4983230072969 + 3 ^ 40 * 407391 * 2
def baseEnd_407391 : Nat := 23243044146213423837661

theorem tailTrace_407391 : CollatzResearch.WordTrace tailWord_407391 prefixEnd_407391 23243044146213423837661 := by
  unfold tailWord_407391
  simp only [CollatzResearch.WordTrace]
  refine ⟨14858770467099458688614027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9905846978066305792409351 14858770467099458688614027)
  ·
    refine ⟨22288155700649188032921041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14858770467099458688614027 22288155700649188032921041)
    ·
      refine ⟨16716116775486891024690781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22288155700649188032921041 16716116775486891024690781)
      ·
        refine ⟨6268543790807584134259043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16716116775486891024690781 6268543790807584134259043)
        ·
          refine ⟨9402815686211376201388565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6268543790807584134259043 9402815686211376201388565)
          ·
            refine ⟨440756985291158259440089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9402815686211376201388565 440756985291158259440089)
            ·
              refine ⟨330567738968368694580067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440756985291158259440089 330567738968368694580067)
              ·
                refine ⟨495851608452553041870101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330567738968368694580067 495851608452553041870101)
                ·
                  refine ⟨23243044146213423837661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 495851608452553041870101 23243044146213423837661)
                  ·
                    rfl

theorem cell23_407391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 6].length) (baseStart_407391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407391 prefixEnd_407391 := by exact prefixLift 407391
  have htrace : WordTrace (prefixWord ++ tailWord_407391) baseStart_407391 baseEnd_407391 := by
    simpa [prefixWord, tailWord_407391, baseEnd_407391] using wordTrace_append hprefix tailTrace_407391
  have hstable : (prefixWord ++ tailWord_407391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407391).length < 2 ^ (prefixWord ++ tailWord_407391).sum := by decide
  have hdescent : baseEnd_407391 < baseStart_407391 := by decide
  rcases family_descends (prefixWord ++ tailWord_407391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407404 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_407404 : Nat := 118140960795 + 407404 * 2 ^ 59
def prefixEnd_407404 : Nat := 4983230072969 + 3 ^ 40 * 407404 * 2
def baseEnd_407404 : Nat := 69731357521476421225463

theorem tailTrace_407404 : CollatzResearch.WordTrace tailWord_407404 prefixEnd_407404 69731357521476421225463 := by
  unfold tailWord_407404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7429622308026180954418633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9906163077368241272558177 7429622308026180954418633)
  ·
    refine ⟨5572216731019635715813975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7429622308026180954418633 5572216731019635715813975)
    ·
      refine ⟨8358325096529453573720963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572216731019635715813975 8358325096529453573720963)
      ·
        refine ⟨12537487644794180360581445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8358325096529453573720963 12537487644794180360581445)
        ·
          refine ⟨2350778933398908817609021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12537487644794180360581445 2350778933398908817609021)
          ·
            refine ⟨881542100024590806603383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2350778933398908817609021 881542100024590806603383)
            ·
              refine ⟨1322313150036886209905075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881542100024590806603383 1322313150036886209905075)
              ·
                refine ⟨1983469725055329314857613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1322313150036886209905075 1983469725055329314857613)
                ·
                  refine ⟨743801146895748493071605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1983469725055329314857613 743801146895748493071605)
                  ·
                    refine ⟨69731357521476421225463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 743801146895748493071605 69731357521476421225463)
                    ·
                      rfl

theorem cell23_407404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_407404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407404 prefixEnd_407404 := by exact prefixLift 407404
  have htrace : WordTrace (prefixWord ++ tailWord_407404) baseStart_407404 baseEnd_407404 := by
    simpa [prefixWord, tailWord_407404, baseEnd_407404] using wordTrace_append hprefix tailTrace_407404
  have hstable : (prefixWord ++ tailWord_407404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407404).length < 2 ^ (prefixWord ++ tailWord_407404).sum := by decide
  have hdescent : baseEnd_407404 < baseStart_407404 := by decide
  rcases family_descends (prefixWord ++ tailWord_407404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407475 : List Nat := [1, 1, 1, 2, 3, 1, 6, 3, 1, 2, 2]
def baseStart_407475 : Nat := 118140960795 + 407475 * 2 ^ 59
def prefixEnd_407475 : Nat := 4983230072969 + 3 ^ 40 * 407475 * 2
def baseEnd_407475 : Nat := 209230529690898485888563

theorem tailTrace_407475 : CollatzResearch.WordTrace tailWord_407475 prefixEnd_407475 209230529690898485888563 := by
  unfold tailWord_407475
  simp only [CollatzResearch.WordTrace]
  refine ⟨14861834198795141034671879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9907889465863427356447919 14861834198795141034671879)
  ·
    refine ⟨22292751298192711552007819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14861834198795141034671879 22292751298192711552007819)
    ·
      refine ⟨33439126947289067328011729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22292751298192711552007819 33439126947289067328011729)
      ·
        refine ⟨25079345210466800496008797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33439126947289067328011729 25079345210466800496008797)
        ·
          refine ⟨9404754453925050186003299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25079345210466800496008797 9404754453925050186003299)
          ·
            refine ⟨14107131680887575279004949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404754453925050186003299 14107131680887575279004949)
            ·
              refine ⟨661271797541605091203357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14107131680887575279004949 661271797541605091203357)
              ·
                refine ⟨247976924078101909201259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661271797541605091203357 247976924078101909201259)
                ·
                  refine ⟨371965386117152863801889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247976924078101909201259 371965386117152863801889)
                  ·
                    refine ⟨278974039587864647851417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 371965386117152863801889 278974039587864647851417)
                    ·
                      refine ⟨209230529690898485888563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 278974039587864647851417 209230529690898485888563)
                      ·
                        rfl

theorem cell23_407475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 3, 1, 2, 2].length) (baseStart_407475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407475 prefixEnd_407475 := by exact prefixLift 407475
  have htrace : WordTrace (prefixWord ++ tailWord_407475) baseStart_407475 baseEnd_407475 := by
    simpa [prefixWord, tailWord_407475, baseEnd_407475] using wordTrace_append hprefix tailTrace_407475
  have hstable : (prefixWord ++ tailWord_407475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407475).length < 2 ^ (prefixWord ++ tailWord_407475).sum := by decide
  have hdescent : baseEnd_407475 < baseStart_407475 := by decide
  rcases family_descends (prefixWord ++ tailWord_407475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407531 : List Nat := [1, 1, 1, 1, 2, 3, 1, 6, 1, 4, 2]
def baseStart_407531 : Nat := 118140960795 + 407531 * 2 ^ 59
def prefixEnd_407531 : Nat := 4983230072969 + 3 ^ 40 * 407531 * 2
def baseEnd_407531 : Nat := 209259284607550266788305

theorem tailTrace_407531 : CollatzResearch.WordTrace tailWord_407531 prefixEnd_407531 209259284607550266788305 := by
  unfold tailWord_407531
  simp only [CollatzResearch.WordTrace]
  refine ⟨14863876686592262598710447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9909251124394841732473631 14863876686592262598710447)
  ·
    refine ⟨22295815029888393898065671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14863876686592262598710447 22295815029888393898065671)
    ·
      refine ⟨33443722544832590847098507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22295815029888393898065671 33443722544832590847098507)
      ·
        refine ⟨50165583817248886270647761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33443722544832590847098507 50165583817248886270647761)
        ·
          refine ⟨37624187862936664702985821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50165583817248886270647761 37624187862936664702985821)
          ·
            refine ⟨14109070448601249263619683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37624187862936664702985821 14109070448601249263619683)
            ·
              refine ⟨21163605672901873895429525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14109070448601249263619683 21163605672901873895429525)
              ·
                refine ⟨992044015917275338848259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21163605672901873895429525 992044015917275338848259)
                ·
                  refine ⟨1488066023875913008272389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 992044015917275338848259 1488066023875913008272389)
                  ·
                    refine ⟨279012379476733689051073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1488066023875913008272389 279012379476733689051073)
                    ·
                      refine ⟨209259284607550266788305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279012379476733689051073 209259284607550266788305)
                      ·
                        rfl

theorem cell23_407531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 6, 1, 4, 2].length) (baseStart_407531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407531 prefixEnd_407531 := by exact prefixLift 407531
  have htrace : WordTrace (prefixWord ++ tailWord_407531) baseStart_407531 baseEnd_407531 := by
    simpa [prefixWord, tailWord_407531, baseEnd_407531] using wordTrace_append hprefix tailTrace_407531
  have hstable : (prefixWord ++ tailWord_407531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407531).length < 2 ^ (prefixWord ++ tailWord_407531).sum := by decide
  have hdescent : baseEnd_407531 < baseStart_407531 := by decide
  rcases family_descends (prefixWord ++ tailWord_407531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407544 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_407544 : Nat := 118140960795 + 407544 * 2 ^ 59
def prefixEnd_407544 : Nat := 4983230072969 + 3 ^ 40 * 407544 * 2
def baseEnd_407544 : Nat := 209265959856058715925745

theorem tailTrace_407544 : CollatzResearch.WordTrace tailWord_407544 prefixEnd_407544 209265959856058715925745 := by
  unfold tailWord_407544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432175417772582909466843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9909567223696777212622457 7432175417772582909466843)
  ·
    refine ⟨11148263126658874364200265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7432175417772582909466843 11148263126658874364200265)
    ·
      refine ⟨8361197344994155773150199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11148263126658874364200265 8361197344994155773150199)
      ·
        refine ⟨12541796017491233659725299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8361197344994155773150199 12541796017491233659725299)
        ·
          refine ⟨18812694026236850489587949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12541796017491233659725299 18812694026236850489587949)
          ·
            refine ⟨7054760259838818933595481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18812694026236850489587949 7054760259838818933595481)
            ·
              refine ⟨5291070194879114200196611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054760259838818933595481 5291070194879114200196611)
              ·
                refine ⟨7936605292318671300294917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5291070194879114200196611 7936605292318671300294917)
                ·
                  refine ⟨1488113492309750868805297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7936605292318671300294917 1488113492309750868805297)
                  ·
                    refine ⟨1116085119232313151603973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488113492309750868805297 1116085119232313151603973)
                    ·
                      refine ⟨209265959856058715925745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1116085119232313151603973 209265959856058715925745)
                      ·
                        rfl

theorem cell23_407544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_407544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407544 prefixEnd_407544 := by exact prefixLift 407544
  have htrace : WordTrace (prefixWord ++ tailWord_407544) baseStart_407544 baseEnd_407544 := by
    simpa [prefixWord, tailWord_407544, baseEnd_407544] using wordTrace_append hprefix tailTrace_407544
  have hstable : (prefixWord ++ tailWord_407544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407544).length < 2 ^ (prefixWord ++ tailWord_407544).sum := by decide
  have hdescent : baseEnd_407544 < baseStart_407544 := by decide
  rcases family_descends (prefixWord ++ tailWord_407544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407548 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_407548 : Nat := 118140960795 + 407548 * 2 ^ 59
def prefixEnd_407548 : Nat := 4983230072969 + 3 ^ 40 * 407548 * 2
def baseEnd_407548 : Nat := 209268013778676700275727

theorem tailTrace_407548 : CollatzResearch.WordTrace tailWord_407548 prefixEnd_407548 209268013778676700275727 := by
  unfold tailWord_407548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432248363765337251039649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9909664485020449668052865 7432248363765337251039649)
  ·
    refine ⟨5574186272824002938279737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7432248363765337251039649 5574186272824002938279737)
    ·
      refine ⟨4180639704618002203709803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5574186272824002938279737 4180639704618002203709803)
      ·
        refine ⟨6270959556927003305564705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4180639704618002203709803 6270959556927003305564705)
        ·
          refine ⟨4703219667695252479173529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6270959556927003305564705 4703219667695252479173529)
          ·
            refine ⟨3527414750771439359380147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703219667695252479173529 3527414750771439359380147)
            ·
              refine ⟨5291122126157159039070221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3527414750771439359380147 5291122126157159039070221)
              ·
                refine ⟨1984170797308934639651333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5291122126157159039070221 1984170797308934639651333)
                ·
                  refine ⟨372032024495425244934625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1984170797308934639651333 372032024495425244934625)
                  ·
                    refine ⟨279024018371568933700969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 372032024495425244934625 279024018371568933700969)
                    ·
                      refine ⟨209268013778676700275727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279024018371568933700969 209268013778676700275727)
                      ·
                        rfl

theorem cell23_407548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_407548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407548 prefixEnd_407548 := by exact prefixLift 407548
  have htrace : WordTrace (prefixWord ++ tailWord_407548) baseStart_407548 baseEnd_407548 := by
    simpa [prefixWord, tailWord_407548, baseEnd_407548] using wordTrace_append hprefix tailTrace_407548
  have hstable : (prefixWord ++ tailWord_407548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407548).length < 2 ^ (prefixWord ++ tailWord_407548).sum := by decide
  have hdescent : baseEnd_407548 < baseStart_407548 := by decide
  rcases family_descends (prefixWord ++ tailWord_407548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407601 : List Nat := [1, 2, 2, 3, 1, 3, 2, 2, 2, 5]
def baseStart_407601 : Nat := 118140960795 + 407601 * 2 ^ 59
def prefixEnd_407601 : Nat := 4983230072969 + 3 ^ 40 * 407601 * 2
def baseEnd_407601 : Nat := 69765076084454997637661

theorem tailTrace_407601 : CollatzResearch.WordTrace tailWord_407601 prefixEnd_407601 69765076084454997637661 := by
  unfold tailWord_407601
  simp only [CollatzResearch.WordTrace]
  refine ⟨14866429796338664553758657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9910953197559109702505771 14866429796338664553758657)
  ·
    refine ⟨11149822347253998415318993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14866429796338664553758657 11149822347253998415318993)
    ·
      refine ⟨8362366760440498811489245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11149822347253998415318993 8362366760440498811489245)
      ·
        refine ⟨3135887535165187054308467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8362366760440498811489245 3135887535165187054308467)
        ·
          refine ⟨4703831302747780581462701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135887535165187054308467 4703831302747780581462701)
          ·
            refine ⟨1763936738530417718048513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4703831302747780581462701 1763936738530417718048513)
            ·
              refine ⟨1322952553897813288536385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763936738530417718048513 1322952553897813288536385)
              ·
                refine ⟨992214415423359966402289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1322952553897813288536385 992214415423359966402289)
                ·
                  refine ⟨744160811567519974801717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 992214415423359966402289 744160811567519974801717)
                  ·
                    refine ⟨69765076084454997637661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 744160811567519974801717 69765076084454997637661)
                    ·
                      rfl

theorem cell23_407601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_407601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407601 prefixEnd_407601 := by exact prefixLift 407601
  have htrace : WordTrace (prefixWord ++ tailWord_407601) baseStart_407601 baseEnd_407601 := by
    simpa [prefixWord, tailWord_407601, baseEnd_407601] using wordTrace_append hprefix tailTrace_407601
  have hstable : (prefixWord ++ tailWord_407601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407601).length < 2 ^ (prefixWord ++ tailWord_407601).sum := by decide
  have hdescent : baseEnd_407601 < baseStart_407601 := by decide
  rcases family_descends (prefixWord ++ tailWord_407601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407631 : List Nat := [1, 1, 2, 1, 1, 2, 2, 6, 3, 4]
def baseStart_407631 : Nat := 118140960795 + 407631 * 2 ^ 59
def prefixEnd_407631 : Nat := 4983230072969 + 3 ^ 40 * 407631 * 2
def baseEnd_407631 : Nat := 69770210890999958512615

theorem tailTrace_407631 : CollatzResearch.WordTrace tailWord_407631 prefixEnd_407631 69770210890999958512615 := by
  unfold tailWord_407631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867523986229979677350747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911682657486653118233831 14867523986229979677350747)
  ·
    refine ⟨22301285979344969516026121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14867523986229979677350747 22301285979344969516026121)
    ·
      refine ⟨16725964484508727137019591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22301285979344969516026121 16725964484508727137019591)
      ·
        refine ⟨25088946726763090705529387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16725964484508727137019591 25088946726763090705529387)
        ·
          refine ⟨37633420090144636058294081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25088946726763090705529387 37633420090144636058294081)
          ·
            refine ⟨28225065067608477043720561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37633420090144636058294081 28225065067608477043720561)
            ·
              refine ⟨21168798800706357782790421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28225065067608477043720561 21168798800706357782790421)
              ·
                refine ⟨992287443783110521068301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21168798800706357782790421 992287443783110521068301)
                ·
                  refine ⟨372107791418666445400613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 992287443783110521068301 372107791418666445400613)
                  ·
                    refine ⟨69770210890999958512615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372107791418666445400613 69770210890999958512615)
                    ·
                      rfl

theorem cell23_407631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 3, 4].length) (baseStart_407631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407631 prefixEnd_407631 := by exact prefixLift 407631
  have htrace : WordTrace (prefixWord ++ tailWord_407631) baseStart_407631 baseEnd_407631 := by
    simpa [prefixWord, tailWord_407631, baseEnd_407631] using wordTrace_append hprefix tailTrace_407631
  have hstable : (prefixWord ++ tailWord_407631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407631).length < 2 ^ (prefixWord ++ tailWord_407631).sum := by decide
  have hdescent : baseEnd_407631 < baseStart_407631 := by decide
  rcases family_descends (prefixWord ++ tailWord_407631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407641 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 3]
def baseStart_407641 : Nat := 118140960795 + 407641 * 2 ^ 59
def prefixEnd_407641 : Nat := 4983230072969 + 3 ^ 40 * 407641 * 2
def baseEnd_407641 : Nat := 209315767479544836412799

theorem tailTrace_407641 : CollatzResearch.WordTrace tailWord_407641 prefixEnd_407641 209315767479544836412799 := by
  unfold tailWord_407641
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867888716193751385214777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911925810795834256809851 14867888716193751385214777)
  ·
    refine ⟨11150916537145313538911083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14867888716193751385214777 11150916537145313538911083)
    ·
      refine ⟨16726374805717970308366625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11150916537145313538911083 16726374805717970308366625)
      ·
        refine ⟨12544781104288477731274969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16726374805717970308366625 12544781104288477731274969)
        ·
          refine ⟨9408585828216358298456227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12544781104288477731274969 9408585828216358298456227)
          ·
            refine ⟨14112878742324537447684341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9408585828216358298456227 14112878742324537447684341)
            ·
              refine ⟨1323082382092925385720407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14112878742324537447684341 1323082382092925385720407)
              ·
                refine ⟨1984623573139388078580611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323082382092925385720407 1984623573139388078580611)
                ·
                  refine ⟨2976935359709082117870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1984623573139388078580611 2976935359709082117870917)
                  ·
                    refine ⟨558175379945452897100797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2976935359709082117870917 558175379945452897100797)
                    ·
                      refine ⟨209315767479544836412799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 558175379945452897100797 209315767479544836412799)
                      ·
                        rfl

theorem cell23_407641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_407641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407641 prefixEnd_407641 := by exact prefixLift 407641
  have htrace : WordTrace (prefixWord ++ tailWord_407641) baseStart_407641 baseEnd_407641 := by
    simpa [prefixWord, tailWord_407641, baseEnd_407641] using wordTrace_append hprefix tailTrace_407641
  have hstable : (prefixWord ++ tailWord_407641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407641).length < 2 ^ (prefixWord ++ tailWord_407641).sum := by decide
  have hdescent : baseEnd_407641 < baseStart_407641 := by decide
  rcases family_descends (prefixWord ++ tailWord_407641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407661 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 8]
def baseStart_407661 : Nat := 118140960795 + 407661 * 2 ^ 59
def prefixEnd_407661 : Nat := 4983230072969 + 3 ^ 40 * 407661 * 2
def baseEnd_407661 : Nat := 23258448565848306462523

theorem tailTrace_407661 : CollatzResearch.WordTrace tailWord_407661 prefixEnd_407661 23258448565848306462523 := by
  unfold tailWord_407661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868618176121294800942837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9912412117414196533961891 14868618176121294800942837)
  ·
    refine ⟨1393932954011371387588391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14868618176121294800942837 1393932954011371387588391)
    ·
      refine ⟨2090899431017057081382587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1393932954011371387588391 2090899431017057081382587)
      ·
        refine ⟨3136349146525585622073881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2090899431017057081382587 3136349146525585622073881)
        ·
          refine ⟨2352261859894189216555411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136349146525585622073881 2352261859894189216555411)
          ·
            refine ⟨3528392789841283824833117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352261859894189216555411 3528392789841283824833117)
            ·
              refine ⟨1323147296190481434312419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3528392789841283824833117 1323147296190481434312419)
              ·
                refine ⟨1984720944285722151468629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1323147296190481434312419 1984720944285722151468629)
                ·
                  refine ⟨23258448565848306462523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1984720944285722151468629 23258448565848306462523)
                  ·
                    rfl

theorem cell23_407661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_407661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407661 prefixEnd_407661 := by exact prefixLift 407661
  have htrace : WordTrace (prefixWord ++ tailWord_407661) baseStart_407661 baseEnd_407661 := by
    simpa [prefixWord, tailWord_407661, baseEnd_407661] using wordTrace_append hprefix tailTrace_407661
  have hstable : (prefixWord ++ tailWord_407661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407661).length < 2 ^ (prefixWord ++ tailWord_407661).sum := by decide
  have hdescent : baseEnd_407661 < baseStart_407661 := by decide
  rcases family_descends (prefixWord ++ tailWord_407661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407708 : List Nat := [2, 2, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_407708 : Nat := 118140960795 + 407708 * 2 ^ 59
def prefixEnd_407708 : Nat := 4983230072969 + 3 ^ 40 * 407708 * 2
def baseEnd_407708 : Nat := 69783390227798691424997

theorem tailTrace_407708 : CollatzResearch.WordTrace tailWord_407708 prefixEnd_407708 69783390227798691424997 := by
  unfold tailWord_407708
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435166203475510913951889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9913554937967347885269185 7435166203475510913951889)
  ·
    refine ⟨5576374652606633185463917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7435166203475510913951889 5576374652606633185463917)
    ·
      refine ⟨2091140494727487444548969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5576374652606633185463917 2091140494727487444548969)
      ·
        refine ⟨1568355371045615583411727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091140494727487444548969 1568355371045615583411727)
        ·
          refine ⟨2352533056568423375117591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568355371045615583411727 2352533056568423375117591)
          ·
            refine ⟨3528799584852635062676387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2352533056568423375117591 3528799584852635062676387)
            ·
              refine ⟨5293199377278952594014581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3528799584852635062676387 5293199377278952594014581)
              ·
                refine ⟨496237441619901805688867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5293199377278952594014581 496237441619901805688867)
                ·
                  refine ⟨744356162429852708533301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496237441619901805688867 744356162429852708533301)
                  ·
                    refine ⟨69783390227798691424997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 744356162429852708533301 69783390227798691424997)
                    ·
                      rfl

theorem cell23_407708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_407708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407708 prefixEnd_407708 := by exact prefixLift 407708
  have htrace : WordTrace (prefixWord ++ tailWord_407708) baseStart_407708 baseEnd_407708 := by
    simpa [prefixWord, tailWord_407708, baseEnd_407708] using wordTrace_append hprefix tailTrace_407708
  have hstable : (prefixWord ++ tailWord_407708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407708).length < 2 ^ (prefixWord ++ tailWord_407708).sum := by decide
  have hdescent : baseEnd_407708 < baseStart_407708 := by decide
  rcases family_descends (prefixWord ++ tailWord_407708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407731 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3]
def baseStart_407731 : Nat := 118140960795 + 407731 * 2 ^ 59
def prefixEnd_407731 : Nat := 4983230072969 + 3 ^ 40 * 407731 * 2
def baseEnd_407731 : Nat := 209361980738449484287385

theorem tailTrace_407731 : CollatzResearch.WordTrace tailWord_407731 prefixEnd_407731 209361980738449484287385 := by
  unfold tailWord_407731
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871171285867696755991047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9914114190578464503994031 14871171285867696755991047)
  ·
    refine ⟨22306756928801545133986571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14871171285867696755991047 22306756928801545133986571)
    ·
      refine ⟨33460135393202317700979857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22306756928801545133986571 33460135393202317700979857)
      ·
        refine ⟨25095101544901738275734893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33460135393202317700979857 25095101544901738275734893)
        ·
          refine ⟨9410663079338151853400585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25095101544901738275734893 9410663079338151853400585)
          ·
            refine ⟨7057997309503613890050439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9410663079338151853400585 7057997309503613890050439)
            ·
              refine ⟨10586995964255420835075659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7057997309503613890050439 10586995964255420835075659)
              ·
                refine ⟨15880493946383131252613489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10586995964255420835075659 15880493946383131252613489)
                ·
                  refine ⟨11910370459787348439460117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15880493946383131252613489 11910370459787348439460117)
                  ·
                    refine ⟨558298615302531958099693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11910370459787348439460117 558298615302531958099693)
                    ·
                      refine ⟨209361980738449484287385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 558298615302531958099693 209361980738449484287385)
                      ·
                        rfl

theorem cell23_407731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 3].length) (baseStart_407731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407731 prefixEnd_407731 := by exact prefixLift 407731
  have htrace : WordTrace (prefixWord ++ tailWord_407731) baseStart_407731 baseEnd_407731 := by
    simpa [prefixWord, tailWord_407731, baseEnd_407731] using wordTrace_append hprefix tailTrace_407731
  have hstable : (prefixWord ++ tailWord_407731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407731).length < 2 ^ (prefixWord ++ tailWord_407731).sum := by decide
  have hdescent : baseEnd_407731 < baseStart_407731 := by decide
  rcases family_descends (prefixWord ++ tailWord_407731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407742 : List Nat := [4, 2, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_407742 : Nat := 118140960795 + 407742 * 2 ^ 59
def prefixEnd_407742 : Nat := 4983230072969 + 3 ^ 40 * 407742 * 2
def baseEnd_407742 : Nat := 69789209675216313749945

theorem tailTrace_407742 : CollatzResearch.WordTrace tailWord_407742 prefixEnd_407742 69789209675216313749945 := by
  unfold tailWord_407742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858946561103480704330185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9914381659218563756427653 1858946561103480704330185)
  ·
    refine ⟨1394209920827610528247639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1858946561103480704330185 1394209920827610528247639)
    ·
      refine ⟨2091314881241415792371459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1394209920827610528247639 2091314881241415792371459)
      ·
        refine ⟨3136972321862123688557189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2091314881241415792371459 3136972321862123688557189)
        ·
          refine ⟨588182310349148191604473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3136972321862123688557189 588182310349148191604473)
          ·
            refine ⟨441136732761861143703355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588182310349148191604473 441136732761861143703355)
            ·
              refine ⟨661705099142791715555033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441136732761861143703355 661705099142791715555033)
              ·
                refine ⟨496278824357093786666275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661705099142791715555033 496278824357093786666275)
                ·
                  refine ⟨744418236535640679999413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496278824357093786666275 744418236535640679999413)
                  ·
                    refine ⟨69789209675216313749945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 744418236535640679999413 69789209675216313749945)
                    ·
                      rfl

theorem cell23_407742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_407742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407742 prefixEnd_407742 := by exact prefixLift 407742
  have htrace : WordTrace (prefixWord ++ tailWord_407742) baseStart_407742 baseEnd_407742 := by
    simpa [prefixWord, tailWord_407742, baseEnd_407742] using wordTrace_append hprefix tailTrace_407742
  have hstable : (prefixWord ++ tailWord_407742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407742).length < 2 ^ (prefixWord ++ tailWord_407742).sum := by decide
  have hdescent : baseEnd_407742 < baseStart_407742 := by decide
  rcases family_descends (prefixWord ++ tailWord_407742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407758 : List Nat := [4, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_407758 : Nat := 118140960795 + 407758 * 2 ^ 59
def prefixEnd_407758 : Nat := 4983230072969 + 3 ^ 40 * 407758 * 2
def baseEnd_407758 : Nat := 209375844716120878649761

theorem tailTrace_407758 : CollatzResearch.WordTrace tailWord_407758 prefixEnd_407758 209375844716120878649761 := by
  unfold tailWord_407758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859019507096235045902991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9914770704513253578149285 1859019507096235045902991)
  ·
    refine ⟨2788529260644352568854487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859019507096235045902991 2788529260644352568854487)
    ·
      refine ⟨4182793890966528853281731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788529260644352568854487 4182793890966528853281731)
      ·
        refine ⟨6274190836449793279922597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4182793890966528853281731 6274190836449793279922597)
        ·
          refine ⟨1176410781834336239985487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6274190836449793279922597 1176410781834336239985487)
          ·
            refine ⟨1764616172751504359978231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176410781834336239985487 1764616172751504359978231)
            ·
              refine ⟨2646924259127256539967347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1764616172751504359978231 2646924259127256539967347)
              ·
                refine ⟨3970386388690884809951021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2646924259127256539967347 3970386388690884809951021)
                ·
                  refine ⟨1488894895759081803731633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3970386388690884809951021 1488894895759081803731633)
                  ·
                    refine ⟨1116671171819311352798725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1488894895759081803731633 1116671171819311352798725)
                    ·
                      refine ⟨209375844716120878649761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1116671171819311352798725 209375844716120878649761)
                      ·
                        rfl

theorem cell23_407758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_407758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407758 prefixEnd_407758 := by exact prefixLift 407758
  have htrace : WordTrace (prefixWord ++ tailWord_407758) baseStart_407758 baseEnd_407758 := by
    simpa [prefixWord, tailWord_407758, baseEnd_407758] using wordTrace_append hprefix tailTrace_407758
  have hstable : (prefixWord ++ tailWord_407758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407758).length < 2 ^ (prefixWord ++ tailWord_407758).sum := by decide
  have hdescent : baseEnd_407758 < baseStart_407758 := by decide
  rcases family_descends (prefixWord ++ tailWord_407758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407762 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 1, 1, 4]
def baseStart_407762 : Nat := 118140960795 + 407762 * 2 ^ 59
def prefixEnd_407762 : Nat := 4983230072969 + 3 ^ 40 * 407762 * 2
def baseEnd_407762 : Nat := 209377898638738862999743

theorem tailTrace_407762 : CollatzResearch.WordTrace tailWord_407762 prefixEnd_407762 209377898638738862999743 := by
  unfold tailWord_407762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718075487188847262592385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9914867965836926033579693 3718075487188847262592385)
  ·
    refine ⟨2788556615391635446944289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3718075487188847262592385 2788556615391635446944289)
    ·
      refine ⟨2091417461543726585208217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2788556615391635446944289 2091417461543726585208217)
      ·
        refine ⟨1568563096157794938906163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2091417461543726585208217 1568563096157794938906163)
        ·
          refine ⟨2352844644236692408359245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568563096157794938906163 2352844644236692408359245)
          ·
            refine ⟨882316741588759653134717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2352844644236692408359245 882316741588759653134717)
            ·
              refine ⟨330868778095784869925519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 882316741588759653134717 330868778095784869925519)
              ·
                refine ⟨496303167143677304888279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 330868778095784869925519 496303167143677304888279)
                ·
                  refine ⟨744454750715515957332419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496303167143677304888279 744454750715515957332419)
                  ·
                    refine ⟨1116682126073273935998629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 744454750715515957332419 1116682126073273935998629)
                    ·
                      refine ⟨209377898638738862999743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1116682126073273935998629 209377898638738862999743)
                      ·
                        rfl

theorem cell23_407762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_407762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407762 prefixEnd_407762 := by exact prefixLift 407762
  have htrace : WordTrace (prefixWord ++ tailWord_407762) baseStart_407762 baseEnd_407762 := by
    simpa [prefixWord, tailWord_407762, baseEnd_407762] using wordTrace_append hprefix tailTrace_407762
  have hstable : (prefixWord ++ tailWord_407762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407762).length < 2 ^ (prefixWord ++ tailWord_407762).sum := by decide
  have hdescent : baseEnd_407762 < baseStart_407762 := by decide
  rcases family_descends (prefixWord ++ tailWord_407762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407795 : List Nat := [1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 3]
def baseStart_407795 : Nat := 118140960795 + 407795 * 2 ^ 59
def prefixEnd_407795 : Nat := 4983230072969 + 3 ^ 40 * 407795 * 2
def baseEnd_407795 : Nat := 209394843500337233887091

theorem tailTrace_407795 : CollatzResearch.WordTrace tailWord_407795 prefixEnd_407795 209394843500337233887091 := by
  unfold tailWord_407795
  simp only [CollatzResearch.WordTrace]
  refine ⟨14873505557635835686320839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9915670371757223790880559 14873505557635835686320839)
  ·
    refine ⟨22310258336453753529481259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14873505557635835686320839 22310258336453753529481259)
    ·
      refine ⟨33465387504680630294221889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22310258336453753529481259 33465387504680630294221889)
      ·
        refine ⟨25099040628510472720666417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33465387504680630294221889 25099040628510472720666417)
        ·
          refine ⟨18824280471382854540499813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25099040628510472720666417 18824280471382854540499813)
          ·
            refine ⟨3529552588384285226343715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18824280471382854540499813 3529552588384285226343715)
            ·
              refine ⟨5294328882576427839515573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529552588384285226343715 5294328882576427839515573)
              ·
                refine ⟨496343332741540109954585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5294328882576427839515573 496343332741540109954585)
                ·
                  refine ⟨372257499556155082465939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496343332741540109954585 372257499556155082465939)
                  ·
                    refine ⟨558386249334232623698909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 372257499556155082465939 558386249334232623698909)
                    ·
                      refine ⟨209394843500337233887091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 558386249334232623698909 209394843500337233887091)
                      ·
                        rfl

theorem cell23_407795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2, 1, 3].length) (baseStart_407795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407795 prefixEnd_407795 := by exact prefixLift 407795
  have htrace : WordTrace (prefixWord ++ tailWord_407795) baseStart_407795 baseEnd_407795 := by
    simpa [prefixWord, tailWord_407795, baseEnd_407795] using wordTrace_append hprefix tailTrace_407795
  have hstable : (prefixWord ++ tailWord_407795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407795).length < 2 ^ (prefixWord ++ tailWord_407795).sum := by decide
  have hdescent : baseEnd_407795 < baseStart_407795 := by decide
  rcases family_descends (prefixWord ++ tailWord_407795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407811 : List Nat := [1, 1, 1, 3, 2, 3, 1, 2, 1, 8]
def baseStart_407811 : Nat := 118140960795 + 407811 * 2 ^ 59
def prefixEnd_407811 : Nat := 4983230072969 + 3 ^ 40 * 407811 * 2
def baseEnd_407811 : Nat := 69801019730269723762339

theorem tailTrace_407811 : CollatzResearch.WordTrace tailWord_407811 prefixEnd_407811 69801019730269723762339 := by
  unfold tailWord_407811
  simp only [CollatzResearch.WordTrace]
  refine ⟨14874089125577870418903287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9916059417051913612602191 14874089125577870418903287)
  ·
    refine ⟨22311133688366805628354931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14874089125577870418903287 22311133688366805628354931)
    ·
      refine ⟨33466700532550208442532397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22311133688366805628354931 33466700532550208442532397)
      ·
        refine ⟨12550012699706328165949649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33466700532550208442532397 12550012699706328165949649)
        ·
          refine ⟨9412509524779746124462237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12550012699706328165949649 9412509524779746124462237)
          ·
            refine ⟨3529691071792404796673339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9412509524779746124462237 3529691071792404796673339)
            ·
              refine ⟨5294536607688607195010009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3529691071792404796673339 5294536607688607195010009)
              ·
                refine ⟨3970902455766455396257507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5294536607688607195010009 3970902455766455396257507)
                ·
                  refine ⟨5956353683649683094386261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3970902455766455396257507 5956353683649683094386261)
                  ·
                    refine ⟨69801019730269723762339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5956353683649683094386261 69801019730269723762339)
                    ·
                      rfl

theorem cell23_407811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 8].length) (baseStart_407811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407811 prefixEnd_407811 := by exact prefixLift 407811
  have htrace : WordTrace (prefixWord ++ tailWord_407811) baseStart_407811 baseEnd_407811 := by
    simpa [prefixWord, tailWord_407811, baseEnd_407811] using wordTrace_append hprefix tailTrace_407811
  have hstable : (prefixWord ++ tailWord_407811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407811).length < 2 ^ (prefixWord ++ tailWord_407811).sum := by decide
  have hdescent : baseEnd_407811 < baseStart_407811 := by decide
  rcases family_descends (prefixWord ++ tailWord_407811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407822 : List Nat := [4, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_407822 : Nat := 118140960795 + 407822 * 2 ^ 59
def prefixEnd_407822 : Nat := 4983230072969 + 3 ^ 40 * 407822 * 2
def baseEnd_407822 : Nat := 209408707478008628249467

theorem tailTrace_407822 : CollatzResearch.WordTrace tailWord_407822 prefixEnd_407822 209408707478008628249467 := by
  unfold tailWord_407822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1859311291067252412194215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9916326885692012865035813 1859311291067252412194215)
  ·
    refine ⟨2788966936600878618291323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1859311291067252412194215 2788966936600878618291323)
    ·
      refine ⟨4183450404901317927436985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2788966936600878618291323 4183450404901317927436985)
      ·
        refine ⟨3137587803675988445577739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4183450404901317927436985 3137587803675988445577739)
        ·
          refine ⟨4706381705513982668366609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3137587803675988445577739 4706381705513982668366609)
          ·
            refine ⟨3529786279135487001274957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4706381705513982668366609 3529786279135487001274957)
            ·
              refine ⟨1323669854675807625478109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3529786279135487001274957 1323669854675807625478109)
              ·
                refine ⟨496376195503427859554291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1323669854675807625478109 496376195503427859554291)
                ·
                  refine ⟨744564293255141789331437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496376195503427859554291 744564293255141789331437)
                  ·
                    refine ⟨279211609970678170999289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 744564293255141789331437 279211609970678170999289)
                    ·
                      refine ⟨209408707478008628249467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279211609970678170999289 209408707478008628249467)
                      ·
                        rfl

theorem cell23_407822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_407822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407822 prefixEnd_407822 := by exact prefixLift 407822
  have htrace : WordTrace (prefixWord ++ tailWord_407822) baseStart_407822 baseEnd_407822 := by
    simpa [prefixWord, tailWord_407822, baseEnd_407822] using wordTrace_append hprefix tailTrace_407822
  have hstable : (prefixWord ++ tailWord_407822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407822).length < 2 ^ (prefixWord ++ tailWord_407822).sum := by decide
  have hdescent : baseEnd_407822 < baseStart_407822 := by decide
  rcases family_descends (prefixWord ++ tailWord_407822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407852 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_407852 : Nat := 118140960795 + 407852 * 2 ^ 59
def prefixEnd_407852 : Nat := 4983230072969 + 3 ^ 40 * 407852 * 2
def baseEnd_407852 : Nat := 209424111897643510874329

theorem tailTrace_407852 : CollatzResearch.WordTrace tailWord_407852 prefixEnd_407852 209424111897643510874329 := by
  unfold tailWord_407852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437792259214667210572905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9917056345619556280763873 7437792259214667210572905)
  ·
    refine ⟨5578344194411000407929679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7437792259214667210572905 5578344194411000407929679)
    ·
      refine ⟨8367516291616500611894519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5578344194411000407929679 8367516291616500611894519)
      ·
        refine ⟨12551274437424750917841779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8367516291616500611894519 12551274437424750917841779)
        ·
          refine ⟨18826911656137126376762669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12551274437424750917841779 18826911656137126376762669)
          ·
            refine ⟨7060091871051422391286001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18826911656137126376762669 7060091871051422391286001)
            ·
              refine ⟨5295068903288566793464501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7060091871051422391286001 5295068903288566793464501)
              ·
                refine ⟨496412709683303136887297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5295068903288566793464501 496412709683303136887297)
                ·
                  refine ⟨372309532262477352665473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496412709683303136887297 372309532262477352665473)
                  ·
                    refine ⟨279232149196858014499105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 372309532262477352665473 279232149196858014499105)
                    ·
                      refine ⟨209424111897643510874329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279232149196858014499105 209424111897643510874329)
                      ·
                        rfl

theorem cell23_407852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_407852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407852 prefixEnd_407852 := by exact prefixLift 407852
  have htrace : WordTrace (prefixWord ++ tailWord_407852) baseStart_407852 baseEnd_407852 := by
    simpa [prefixWord, tailWord_407852, baseEnd_407852] using wordTrace_append hprefix tailTrace_407852
  have hstable : (prefixWord ++ tailWord_407852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407852).length < 2 ^ (prefixWord ++ tailWord_407852).sum := by decide
  have hdescent : baseEnd_407852 < baseStart_407852 := by decide
  rcases family_descends (prefixWord ++ tailWord_407852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407875 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 5]
def baseStart_407875 : Nat := 118140960795 + 407875 * 2 ^ 59
def prefixEnd_407875 : Nat := 4983230072969 + 3 ^ 40 * 407875 * 2
def baseEnd_407875 : Nat := 23270657994744102320747

theorem tailTrace_407875 : CollatzResearch.WordTrace tailWord_407875 prefixEnd_407875 23270657994744102320747 := by
  unfold tailWord_407875
  simp only [CollatzResearch.WordTrace]
  refine ⟨14876423397346009349233079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9917615598230672899488719 14876423397346009349233079)
  ·
    refine ⟨22314635096019014023849619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14876423397346009349233079 22314635096019014023849619)
    ·
      refine ⟨33471952644028521035774429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22314635096019014023849619 33471952644028521035774429)
      ·
        refine ⟨12551982241510695388415411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33471952644028521035774429 12551982241510695388415411)
        ·
          refine ⟨18827973362266043082623117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12551982241510695388415411 18827973362266043082623117)
          ·
            refine ⟨7060490010849766155983669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18827973362266043082623117 7060490010849766155983669)
            ·
              refine ⟨661920938517165577123469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7060490010849766155983669 661920938517165577123469)
              ·
                refine ⟨248220351943937091421301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 661920938517165577123469 248220351943937091421301)
                ·
                  refine ⟨23270657994744102320747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248220351943937091421301 23270657994744102320747)
                  ·
                    rfl

theorem cell23_407875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 5].length) (baseStart_407875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407875 prefixEnd_407875 := by exact prefixLift 407875
  have htrace : WordTrace (prefixWord ++ tailWord_407875) baseStart_407875 baseEnd_407875 := by
    simpa [prefixWord, tailWord_407875, baseEnd_407875] using wordTrace_append hprefix tailTrace_407875
  have hstable : (prefixWord ++ tailWord_407875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407875).length < 2 ^ (prefixWord ++ tailWord_407875).sum := by decide
  have hdescent : baseEnd_407875 < baseStart_407875 := by decide
  rcases family_descends (prefixWord ++ tailWord_407875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407888 : List Nat := [2, 1, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_407888 : Nat := 118140960795 + 407888 * 2 ^ 59
def prefixEnd_407888 : Nat := 4983230072969 + 3 ^ 40 * 407888 * 2
def baseEnd_407888 : Nat := 69814199067068456674721

theorem tailTrace_407888 : CollatzResearch.WordTrace tailWord_407888 prefixEnd_407888 69814199067068456674721 := by
  unfold tailWord_407888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438448773149456284728159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9917931697532608379637545 7438448773149456284728159)
  ·
    refine ⟨11157673159724184427092239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7438448773149456284728159 11157673159724184427092239)
    ·
      refine ⟨16736509739586276640638359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11157673159724184427092239 16736509739586276640638359)
      ·
        refine ⟨25104764609379414960957539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16736509739586276640638359 25104764609379414960957539)
        ·
          refine ⟨37657146914069122441436309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25104764609379414960957539 37657146914069122441436309)
          ·
            refine ⟨1765178761596990114442327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 37657146914069122441436309 1765178761596990114442327)
            ·
              refine ⟨2647768142395485171663491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765178761596990114442327 2647768142395485171663491)
              ·
                refine ⟨3971652213593227757495237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647768142395485171663491 3971652213593227757495237)
                ·
                  refine ⟨744684790048730204530357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3971652213593227757495237 744684790048730204530357)
                  ·
                    refine ⟨69814199067068456674721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 744684790048730204530357 69814199067068456674721)
                    ·
                      rfl

theorem cell23_407888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_407888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407888 prefixEnd_407888 := by exact prefixLift 407888
  have htrace : WordTrace (prefixWord ++ tailWord_407888) baseStart_407888 baseEnd_407888 := by
    simpa [prefixWord, tailWord_407888, baseEnd_407888] using wordTrace_append hprefix tailTrace_407888
  have hstable : (prefixWord ++ tailWord_407888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407888).length < 2 ^ (prefixWord ++ tailWord_407888).sum := by decide
  have hdescent : baseEnd_407888 < baseStart_407888 := by decide
  rcases family_descends (prefixWord ++ tailWord_407888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407895 : List Nat := [1, 1, 3, 2, 3, 1, 2, 1, 2, 5, 2]
def baseStart_407895 : Nat := 118140960795 + 407895 * 2 ^ 59
def prefixEnd_407895 : Nat := 4983230072969 + 3 ^ 40 * 407895 * 2
def baseEnd_407895 : Nat := 209446191565786842636631

theorem tailTrace_407895 : CollatzResearch.WordTrace tailWord_407895 prefixEnd_407895 209446191565786842636631 := by
  unfold tailWord_407895
  simp only [CollatzResearch.WordTrace]
  refine ⟨14877152857273552764961139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9918101904849035176640759 14877152857273552764961139)
  ·
    refine ⟨22315729285910329147441709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14877152857273552764961139 22315729285910329147441709)
    ·
      refine ⟨8368398482216373430290641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22315729285910329147441709 8368398482216373430290641)
      ·
        refine ⟨6276298861662280072717981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8368398482216373430290641 6276298861662280072717981)
        ·
          refine ⟨2353612073123355027269243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6276298861662280072717981 2353612073123355027269243)
          ·
            refine ⟨3530418109685032540903865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2353612073123355027269243 3530418109685032540903865)
            ·
              refine ⟨2647813582263774405677899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3530418109685032540903865 2647813582263774405677899)
              ·
                refine ⟨3971720373395661608516849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2647813582263774405677899 3971720373395661608516849)
                ·
                  refine ⟨2978790280046746206387637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3971720373395661608516849 2978790280046746206387637)
                  ·
                    refine ⟨279261588754382456848841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2978790280046746206387637 279261588754382456848841)
                    ·
                      refine ⟨209446191565786842636631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279261588754382456848841 209446191565786842636631)
                      ·
                        rfl

theorem cell23_407895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_407895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407895 prefixEnd_407895 := by exact prefixLift 407895
  have htrace : WordTrace (prefixWord ++ tailWord_407895) baseStart_407895 baseEnd_407895 := by
    simpa [prefixWord, tailWord_407895, baseEnd_407895] using wordTrace_append hprefix tailTrace_407895
  have hstable : (prefixWord ++ tailWord_407895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407895).length < 2 ^ (prefixWord ++ tailWord_407895).sum := by decide
  have hdescent : baseEnd_407895 < baseStart_407895 := by decide
  rcases family_descends (prefixWord ++ tailWord_407895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407969 : List Nat := [1, 2, 3, 5, 1, 1, 1, 2, 3, 4]
def baseStart_407969 : Nat := 118140960795 + 407969 * 2 ^ 59
def prefixEnd_407969 : Nat := 4983230072969 + 3 ^ 40 * 407969 * 2
def baseEnd_407969 : Nat := 69828063044739851037097

theorem tailTrace_407969 : CollatzResearch.WordTrace tailWord_407969 prefixEnd_407969 69828063044739851037097 := by
  unfold tailWord_407969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14879851859005463403154961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9919901239336975602103307 14879851859005463403154961)
  ·
    refine ⟨11159888894254097552366221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14879851859005463403154961 11159888894254097552366221)
    ·
      refine ⟨4184958335345286582137333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11159888894254097552366221 4184958335345286582137333)
      ·
        refine ⟨392339843938620617075375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4184958335345286582137333 392339843938620617075375)
        ·
          refine ⟨588509765907930925613063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392339843938620617075375 588509765907930925613063)
          ·
            refine ⟨882764648861896388419595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588509765907930925613063 882764648861896388419595)
            ·
              refine ⟨1324146973292844582629393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882764648861896388419595 1324146973292844582629393)
              ·
                refine ⟨993110229969633436972045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1324146973292844582629393 993110229969633436972045)
                ·
                  refine ⟨372416336238612538864517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993110229969633436972045 372416336238612538864517)
                  ·
                    refine ⟨69828063044739851037097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372416336238612538864517 69828063044739851037097)
                    ·
                      rfl

theorem cell23_407969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_407969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_407969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_407969 prefixEnd_407969 := by exact prefixLift 407969
  have htrace : WordTrace (prefixWord ++ tailWord_407969) baseStart_407969 baseEnd_407969 := by
    simpa [prefixWord, tailWord_407969, baseEnd_407969] using wordTrace_append hprefix tailTrace_407969
  have hstable : (prefixWord ++ tailWord_407969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407969).length < 2 ^ (prefixWord ++ tailWord_407969).sum := by decide
  have hdescent : baseEnd_407969 < baseStart_407969 := by decide
  rcases family_descends (prefixWord ++ tailWord_407969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408009 : List Nat := [1, 2, 1, 1, 2, 1, 6, 4, 1, 1, 3]
def baseStart_408009 : Nat := 118140960795 + 408009 * 2 ^ 59
def prefixEnd_408009 : Nat := 4983230072969 + 3 ^ 40 * 408009 * 2
def baseEnd_408009 : Nat := 209504728360399396611107

theorem tailTrace_408009 : CollatzResearch.WordTrace tailWord_408009 prefixEnd_408009 209504728360399396611107 := by
  unfold tailWord_408009
  simp only [CollatzResearch.WordTrace]
  refine ⟨14881310778860550234611081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9920873852573700156407387 14881310778860550234611081)
  ·
    refine ⟨11160983084145412675958311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14881310778860550234611081 11160983084145412675958311)
    ·
      refine ⟨16741474626218119013937467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11160983084145412675958311 16741474626218119013937467)
      ·
        refine ⟨25112211939327178520906201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16741474626218119013937467 25112211939327178520906201)
        ·
          refine ⟨18834158954495383890679651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25112211939327178520906201 18834158954495383890679651)
          ·
            refine ⟨28251238431743075836019477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18834158954495383890679651 28251238431743075836019477)
            ·
              refine ⟨1324276801487956679813413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28251238431743075836019477 1324276801487956679813413)
              ·
                refine ⟨248301900278991877465015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1324276801487956679813413 248301900278991877465015)
                ·
                  refine ⟨372452850418487816197523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248301900278991877465015 372452850418487816197523)
                  ·
                    refine ⟨558679275627731724296285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 372452850418487816197523 558679275627731724296285)
                    ·
                      refine ⟨209504728360399396611107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 558679275627731724296285 209504728360399396611107)
                      ·
                        rfl

theorem cell23_408009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 4, 1, 1, 3].length) (baseStart_408009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408009 prefixEnd_408009 := by exact prefixLift 408009
  have htrace : WordTrace (prefixWord ++ tailWord_408009) baseStart_408009 baseEnd_408009 := by
    simpa [prefixWord, tailWord_408009, baseEnd_408009] using wordTrace_append hprefix tailTrace_408009
  have hstable : (prefixWord ++ tailWord_408009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408009).length < 2 ^ (prefixWord ++ tailWord_408009).sum := by decide
  have hdescent : baseEnd_408009 < baseStart_408009 := by decide
  rcases family_descends (prefixWord ++ tailWord_408009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408032 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4]
def baseStart_408032 : Nat := 118140960795 + 408032 * 2 ^ 59
def prefixEnd_408032 : Nat := 4983230072969 + 3 ^ 40 * 408032 * 2
def baseEnd_408032 : Nat := 209516538415452806623501

theorem tailTrace_408032 : CollatzResearch.WordTrace tailWord_408032 prefixEnd_408032 209516538415452806623501 := by
  unfold tailWord_408032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441074828888612581349175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9921433105184816775132233 7441074828888612581349175)
  ·
    refine ⟨11161612243332918872023763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7441074828888612581349175 11161612243332918872023763)
    ·
      refine ⟨16742418364999378308035645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11161612243332918872023763 16742418364999378308035645)
      ·
        refine ⟨6278406886874766865513367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16742418364999378308035645 6278406886874766865513367)
        ·
          refine ⟨9417610330312150298270051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6278406886874766865513367 9417610330312150298270051)
          ·
            refine ⟨14126415495468225447405077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9417610330312150298270051 14126415495468225447405077)
            ·
              refine ⟨662175726350073067847113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14126415495468225447405077 662175726350073067847113)
              ·
                refine ⟨496631794762554800885335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662175726350073067847113 496631794762554800885335)
                ·
                  refine ⟨744947692143832201328003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496631794762554800885335 744947692143832201328003)
                  ·
                    refine ⟨1117421538215748301992005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 744947692143832201328003 1117421538215748301992005)
                    ·
                      refine ⟨209516538415452806623501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1117421538215748301992005 209516538415452806623501)
                      ·
                        rfl

theorem cell23_408032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_408032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408032 prefixEnd_408032 := by exact prefixLift 408032
  have htrace : WordTrace (prefixWord ++ tailWord_408032) baseStart_408032 baseEnd_408032 := by
    simpa [prefixWord, tailWord_408032, baseEnd_408032] using wordTrace_append hprefix tailTrace_408032
  have hstable : (prefixWord ++ tailWord_408032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408032).length < 2 ^ (prefixWord ++ tailWord_408032).sum := by decide
  have hdescent : baseEnd_408032 < baseStart_408032 := by decide
  rcases family_descends (prefixWord ++ tailWord_408032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408042 : List Nat := [3, 1, 3, 1, 3, 1, 1, 2, 4, 4]
def baseStart_408042 : Nat := 118140960795 + 408042 * 2 ^ 59
def prefixEnd_408042 : Nat := 4983230072969 + 3 ^ 40 * 408042 * 2
def baseEnd_408042 : Nat := 69840557740665922499485

theorem tailTrace_408042 : CollatzResearch.WordTrace tailWord_408042 prefixEnd_408042 69840557740665922499485 := by
  unfold tailWord_408042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720628596935249217640595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9921676258493997913708253 3720628596935249217640595)
  ·
    refine ⟨5580942895402873826460893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720628596935249217640595 5580942895402873826460893)
    ·
      refine ⟨2092853585776077684922835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5580942895402873826460893 2092853585776077684922835)
      ·
        refine ⟨3139280378664116527384253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2092853585776077684922835 3139280378664116527384253)
        ·
          refine ⟨1177230141999043697769095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3139280378664116527384253 1177230141999043697769095)
          ·
            refine ⟨1765845212998565546653643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177230141999043697769095 1765845212998565546653643)
            ·
              refine ⟨2648767819497848319980465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765845212998565546653643 2648767819497848319980465)
              ·
                refine ⟨1986575864623386239985349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648767819497848319980465 1986575864623386239985349)
                ·
                  refine ⟨372482974616884919997253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1986575864623386239985349 372482974616884919997253)
                  ·
                    refine ⟨69840557740665922499485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372482974616884919997253 69840557740665922499485)
                    ·
                      rfl

theorem cell23_408042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_408042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408042 prefixEnd_408042 := by exact prefixLift 408042
  have htrace : WordTrace (prefixWord ++ tailWord_408042) baseStart_408042 baseEnd_408042 := by
    simpa [prefixWord, tailWord_408042, baseEnd_408042] using wordTrace_append hprefix tailTrace_408042
  have hstable : (prefixWord ++ tailWord_408042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408042).length < 2 ^ (prefixWord ++ tailWord_408042).sum := by decide
  have hdescent : baseEnd_408042 < baseStart_408042 := by decide
  rcases family_descends (prefixWord ++ tailWord_408042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408076 : List Nat := [2, 2, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_408076 : Nat := 118140960795 + 408076 * 2 ^ 59
def prefixEnd_408076 : Nat := 4983230072969 + 3 ^ 40 * 408076 * 2
def baseEnd_408076 : Nat := 69846377188083544824433

theorem tailTrace_408076 : CollatzResearch.WordTrace tailWord_408076 prefixEnd_408076 69846377188083544824433 := by
  unfold tailWord_408076
  simp only [CollatzResearch.WordTrace]
  refine ⟨7441877234808910338650041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9922502979745213784866721 7441877234808910338650041)
  ·
    refine ⟨5581407926106682753987531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7441877234808910338650041 5581407926106682753987531)
    ·
      refine ⟨8372111889160024130981297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581407926106682753987531 8372111889160024130981297)
      ·
        refine ⟨6279083916870018098235973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8372111889160024130981297 6279083916870018098235973)
        ·
          refine ⟨1177328234413128393419245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6279083916870018098235973 1177328234413128393419245)
          ·
            refine ⟨441498087904923147532217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1177328234413128393419245 441498087904923147532217)
            ·
              refine ⟨331123565928692360649163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441498087904923147532217 331123565928692360649163)
              ·
                refine ⟨496685348893038540973745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331123565928692360649163 496685348893038540973745)
                ·
                  refine ⟨372514011669778905730309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496685348893038540973745 372514011669778905730309)
                  ·
                    refine ⟨69846377188083544824433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372514011669778905730309 69846377188083544824433)
                    ·
                      rfl

theorem cell23_408076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_408076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408076 prefixEnd_408076 := by exact prefixLift 408076
  have htrace : WordTrace (prefixWord ++ tailWord_408076) baseStart_408076 baseEnd_408076 := by
    simpa [prefixWord, tailWord_408076, baseEnd_408076] using wordTrace_append hprefix tailTrace_408076
  have hstable : (prefixWord ++ tailWord_408076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408076).length < 2 ^ (prefixWord ++ tailWord_408076).sum := by decide
  have hdescent : baseEnd_408076 < baseStart_408076 := by decide
  rcases family_descends (prefixWord ++ tailWord_408076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408103 : List Nat := [1, 1, 7, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_408103 : Nat := 118140960795 + 408103 * 2 ^ 59
def prefixEnd_408103 : Nat := 4983230072969 + 3 ^ 40 * 408103 * 2
def baseEnd_408103 : Nat := 209552995541922028835675

theorem tailTrace_408103 : CollatzResearch.WordTrace tailWord_408103 prefixEnd_408103 209552995541922028835675 := by
  unfold tailWord_408103
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884739240520004288532963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9923159493680002859021975 14884739240520004288532963)
  ·
    refine ⟨22327108860780006432799445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14884739240520004288532963 22327108860780006432799445)
    ·
      refine ⟨523291613924531400768737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22327108860780006432799445 523291613924531400768737)
      ·
        refine ⟨392468710443398550576553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523291613924531400768737 392468710443398550576553)
        ·
          refine ⟨294351532832548912932415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392468710443398550576553 294351532832548912932415)
          ·
            refine ⟨441527299248823369398623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294351532832548912932415 441527299248823369398623)
            ·
              refine ⟨662290948873235054097935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441527299248823369398623 662290948873235054097935)
              ·
                refine ⟨993436423309852581146903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662290948873235054097935 993436423309852581146903)
                ·
                  refine ⟨1490154634964778871720355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 993436423309852581146903 1490154634964778871720355)
                  ·
                    refine ⟨2235231952447168307580533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1490154634964778871720355 2235231952447168307580533)
                    ·
                      refine ⟨209552995541922028835675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2235231952447168307580533 209552995541922028835675)
                      ·
                        rfl

theorem cell23_408103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_408103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408103 prefixEnd_408103 := by exact prefixLift 408103
  have htrace : WordTrace (prefixWord ++ tailWord_408103) baseStart_408103 baseEnd_408103 := by
    simpa [prefixWord, tailWord_408103, baseEnd_408103] using wordTrace_append hprefix tailTrace_408103
  have hstable : (prefixWord ++ tailWord_408103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408103).length < 2 ^ (prefixWord ++ tailWord_408103).sum := by decide
  have hdescent : baseEnd_408103 < baseStart_408103 := by decide
  rcases family_descends (prefixWord ++ tailWord_408103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408115 : List Nat := [1, 1, 1, 2, 4, 2, 2, 2, 2, 6]
def baseStart_408115 : Nat := 118140960795 + 408115 * 2 ^ 59
def prefixEnd_408115 : Nat := 4983230072969 + 3 ^ 40 * 408115 * 2
def baseEnd_408115 : Nat := 69853052436591993961873

theorem tailTrace_408115 : CollatzResearch.WordTrace tailWord_408115 prefixEnd_408115 69853052436591993961873 := by
  unfold tailWord_408115
  simp only [CollatzResearch.WordTrace]
  refine ⟨14885176916476530337969799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9923451277651020225313199 14885176916476530337969799)
  ·
    refine ⟨22327765374714795506954699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14885176916476530337969799 22327765374714795506954699)
    ·
      refine ⟨33491648062072193260432049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22327765374714795506954699 33491648062072193260432049)
      ·
        refine ⟨25118736046554144945324037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33491648062072193260432049 25118736046554144945324037)
        ·
          refine ⟨4709763008728902177248257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25118736046554144945324037 4709763008728902177248257)
          ·
            refine ⟨3532322256546676632936193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709763008728902177248257 3532322256546676632936193)
            ·
              refine ⟨2649241692410007474702145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532322256546676632936193 2649241692410007474702145)
              ·
                refine ⟨1986931269307505606026609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649241692410007474702145 1986931269307505606026609)
                ·
                  refine ⟨1490198451980629204519957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1986931269307505606026609 1490198451980629204519957)
                  ·
                    refine ⟨69853052436591993961873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1490198451980629204519957 69853052436591993961873)
                    ·
                      rfl

theorem cell23_408115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2, 2, 6].length) (baseStart_408115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408115 prefixEnd_408115 := by exact prefixLift 408115
  have htrace : WordTrace (prefixWord ++ tailWord_408115) baseStart_408115 baseEnd_408115 := by
    simpa [prefixWord, tailWord_408115, baseEnd_408115] using wordTrace_append hprefix tailTrace_408115
  have hstable : (prefixWord ++ tailWord_408115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408115).length < 2 ^ (prefixWord ++ tailWord_408115).sum := by decide
  have hdescent : baseEnd_408115 < baseStart_408115 := by decide
  rcases family_descends (prefixWord ++ tailWord_408115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408145 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 9]
def baseStart_408145 : Nat := 118140960795 + 408145 * 2 ^ 59
def prefixEnd_408145 : Nat := 4983230072969 + 3 ^ 40 * 408145 * 2
def baseEnd_408145 : Nat := 23286062414378984945609

theorem tailTrace_408145 : CollatzResearch.WordTrace tailWord_408145 prefixEnd_408145 23286062414378984945609 := by
  unfold tailWord_408145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14886271106367845461561889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9924180737578563641041259 14886271106367845461561889)
  ·
    refine ⟨11164703329775884096171417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14886271106367845461561889 11164703329775884096171417)
    ·
      refine ⟨8373527497331913072128563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11164703329775884096171417 8373527497331913072128563)
      ·
        refine ⟨12560291245997869608192845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8373527497331913072128563 12560291245997869608192845)
        ·
          refine ⟨4710109217249201103072317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12560291245997869608192845 4710109217249201103072317)
          ·
            refine ⟨1766290956468450413652119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4710109217249201103072317 1766290956468450413652119)
            ·
              refine ⟨2649436434702675620478179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1766290956468450413652119 2649436434702675620478179)
              ·
                refine ⟨3974154652054013430717269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649436434702675620478179 3974154652054013430717269)
                ·
                  refine ⟨23286062414378984945609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3974154652054013430717269 23286062414378984945609)
                  ·
                    rfl

theorem cell23_408145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 9].length) (baseStart_408145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408145 prefixEnd_408145 := by exact prefixLift 408145
  have htrace : WordTrace (prefixWord ++ tailWord_408145) baseStart_408145 baseEnd_408145 := by
    simpa [prefixWord, tailWord_408145, baseEnd_408145] using wordTrace_append hprefix tailTrace_408145
  have hstable : (prefixWord ++ tailWord_408145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408145).length < 2 ^ (prefixWord ++ tailWord_408145).sum := by decide
  have hdescent : baseEnd_408145 < baseStart_408145 := by decide
  rcases family_descends (prefixWord ++ tailWord_408145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408172 : List Nat := [2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_408172 : Nat := 118140960795 + 408172 * 2 ^ 59
def prefixEnd_408172 : Nat := 4983230072969 + 3 ^ 40 * 408172 * 2
def baseEnd_408172 : Nat := 209588425707082258872857

theorem tailTrace_408172 : CollatzResearch.WordTrace tailWord_408172 prefixEnd_408172 209588425707082258872857 := by
  unfold tailWord_408172
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443627938635014536397385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9924837251513352715196513 7443627938635014536397385)
  ·
    refine ⟨5582720953976260902298039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7443627938635014536397385 5582720953976260902298039)
    ·
      refine ⟨8374081430964391353447059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5582720953976260902298039 8374081430964391353447059)
      ·
        refine ⟨12561122146446587030170589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8374081430964391353447059 12561122146446587030170589)
        ·
          refine ⟨4710420804917470136313971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12561122146446587030170589 4710420804917470136313971)
          ·
            refine ⟨7065631207376205204470957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710420804917470136313971 7065631207376205204470957)
            ·
              refine ⟨2649611702766076951676609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7065631207376205204470957 2649611702766076951676609)
              ·
                refine ⟨1987208777074557713757457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2649611702766076951676609 1987208777074557713757457)
                ·
                  refine ⟨1490406582805918285318093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1987208777074557713757457 1490406582805918285318093)
                  ·
                    refine ⟨558902468552219356994285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1490406582805918285318093 558902468552219356994285)
                    ·
                      refine ⟨209588425707082258872857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 558902468552219356994285 209588425707082258872857)
                      ·
                        rfl

theorem cell23_408172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_408172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408172 prefixEnd_408172 := by exact prefixLift 408172
  have htrace : WordTrace (prefixWord ++ tailWord_408172) baseStart_408172 baseEnd_408172 := by
    simpa [prefixWord, tailWord_408172, baseEnd_408172] using wordTrace_append hprefix tailTrace_408172
  have hstable : (prefixWord ++ tailWord_408172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408172).length < 2 ^ (prefixWord ++ tailWord_408172).sum := by decide
  have hdescent : baseEnd_408172 < baseStart_408172 := by decide
  rcases family_descends (prefixWord ++ tailWord_408172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408173 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_408173 : Nat := 118140960795 + 408173 * 2 ^ 59
def prefixEnd_408173 : Nat := 4983230072969 + 3 ^ 40 * 408173 * 2
def baseEnd_408173 : Nat := 209588939187736754960353

theorem tailTrace_408173 : CollatzResearch.WordTrace tailWord_408173 prefixEnd_408173 209588939187736754960353 := by
  unfold tailWord_408173
  simp only [CollatzResearch.WordTrace]
  refine ⟨14887292350266406243581173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9924861566844270829054115 14887292350266406243581173)
  ·
    refine ⟨1395683657837475585335735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14887292350266406243581173 1395683657837475585335735)
    ·
      refine ⟨2093525486756213378003603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395683657837475585335735 2093525486756213378003603)
      ·
        refine ⟨3140288230134320067005405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093525486756213378003603 3140288230134320067005405)
        ·
          refine ⟨1177608086300370025127027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3140288230134320067005405 1177608086300370025127027)
          ·
            refine ⟨1766412129450555037690541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177608086300370025127027 1766412129450555037690541)
            ·
              refine ⟨662404548543958139133953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766412129450555037690541 662404548543958139133953)
              ·
                refine ⟨496803411407968604350465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662404548543958139133953 496803411407968604350465)
                ·
                  refine ⟨372602558555976453262849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 496803411407968604350465 372602558555976453262849)
                  ·
                    refine ⟨279451918916982339947137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 372602558555976453262849 279451918916982339947137)
                    ·
                      refine ⟨209588939187736754960353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279451918916982339947137 209588939187736754960353)
                      ·
                        rfl

theorem cell23_408173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_408173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408173 prefixEnd_408173 := by exact prefixLift 408173
  have htrace : WordTrace (prefixWord ++ tailWord_408173) baseStart_408173 baseEnd_408173 := by
    simpa [prefixWord, tailWord_408173, baseEnd_408173] using wordTrace_append hprefix tailTrace_408173
  have hstable : (prefixWord ++ tailWord_408173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408173).length < 2 ^ (prefixWord ++ tailWord_408173).sum := by decide
  have hdescent : baseEnd_408173 < baseStart_408173 := by decide
  rcases family_descends (prefixWord ++ tailWord_408173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408239 : List Nat := [1, 1, 2, 1, 2, 5, 3, 1, 3, 4]
def baseStart_408239 : Nat := 118140960795 + 408239 * 2 ^ 59
def prefixEnd_408239 : Nat := 4983230072969 + 3 ^ 40 * 408239 * 2
def baseEnd_408239 : Nat := 69874276303644498911683

theorem tailTrace_408239 : CollatzResearch.WordTrace tailWord_408239 prefixEnd_408239 69874276303644498911683 := by
  unfold tailWord_408239
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889699568027299515483771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9926466378684866343655847 14889699568027299515483771)
  ·
    refine ⟨22334549352040949273225657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889699568027299515483771 22334549352040949273225657)
    ·
      refine ⟨16750912014030711954919243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22334549352040949273225657 16750912014030711954919243)
      ·
        refine ⟨25126368021046067932378865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16750912014030711954919243 25126368021046067932378865)
        ·
          refine ⟨18844776015784550949284149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25126368021046067932378865 18844776015784550949284149)
          ·
            refine ⟨1766697751479801651495389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18844776015784550949284149 1766697751479801651495389)
            ·
              refine ⟨662511656804925619310771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766697751479801651495389 662511656804925619310771)
              ·
                refine ⟨993767485207388428966157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662511656804925619310771 993767485207388428966157)
                ·
                  refine ⟨372662806952770660862309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 993767485207388428966157 372662806952770660862309)
                  ·
                    refine ⟨69874276303644498911683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372662806952770660862309 69874276303644498911683)
                    ·
                      rfl

theorem cell23_408239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 3, 1, 3, 4].length) (baseStart_408239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408239 prefixEnd_408239 := by exact prefixLift 408239
  have htrace : WordTrace (prefixWord ++ tailWord_408239) baseStart_408239 baseEnd_408239 := by
    simpa [prefixWord, tailWord_408239, baseEnd_408239] using wordTrace_append hprefix tailTrace_408239
  have hstable : (prefixWord ++ tailWord_408239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408239).length < 2 ^ (prefixWord ++ tailWord_408239).sum := by decide
  have hdescent : baseEnd_408239 < baseStart_408239 := by decide
  rcases family_descends (prefixWord ++ tailWord_408239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408266 : List Nat := [3, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_408266 : Nat := 118140960795 + 408266 * 2 ^ 59
def prefixEnd_408266 : Nat := 4983230072969 + 3 ^ 40 * 408266 * 2
def baseEnd_408266 : Nat := 209636692888604891097425

theorem tailTrace_408266 : CollatzResearch.WordTrace tailWord_408266 prefixEnd_408266 209636692888604891097425 := by
  unfold tailWord_408266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722671084732370781679163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9927122892619655417811101 3722671084732370781679163)
  ·
    refine ⟨5584006627098556172518745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722671084732370781679163 5584006627098556172518745)
    ·
      refine ⟨4188004970323917129389059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5584006627098556172518745 4188004970323917129389059)
      ·
        refine ⟨6282007455485875694083589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4188004970323917129389059 6282007455485875694083589)
        ·
          refine ⟨1177876397903601692640673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6282007455485875694083589 1177876397903601692640673)
          ·
            refine ⟨883407298427701269480505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1177876397903601692640673 883407298427701269480505)
            ·
              refine ⟨662555473820775952110379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883407298427701269480505 662555473820775952110379)
              ·
                refine ⟨993833210731163928165569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662555473820775952110379 993833210731163928165569)
                ·
                  refine ⟨745374908048372946124177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 993833210731163928165569 745374908048372946124177)
                  ·
                    refine ⟨559031181036279709593133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 745374908048372946124177 559031181036279709593133)
                    ·
                      refine ⟨209636692888604891097425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559031181036279709593133 209636692888604891097425)
                      ·
                        rfl

theorem cell23_408266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_408266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408266 prefixEnd_408266 := by exact prefixLift 408266
  have htrace : WordTrace (prefixWord ++ tailWord_408266) baseStart_408266 baseEnd_408266 := by
    simpa [prefixWord, tailWord_408266, baseEnd_408266] using wordTrace_append hprefix tailTrace_408266
  have hstable : (prefixWord ++ tailWord_408266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408266).length < 2 ^ (prefixWord ++ tailWord_408266).sum := by decide
  have hdescent : baseEnd_408266 < baseStart_408266 := by decide
  rcases family_descends (prefixWord ++ tailWord_408266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408319 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 4]
def baseStart_408319 : Nat := 118140960795 + 408319 * 2 ^ 59
def prefixEnd_408319 : Nat := 4983230072969 + 3 ^ 40 * 408319 * 2
def baseEnd_408319 : Nat := 209663907363293183734681

theorem tailTrace_408319 : CollatzResearch.WordTrace tailWord_408319 prefixEnd_408319 209663907363293183734681 := by
  unfold tailWord_408319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14892617407737473178396011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9928411605158315452264007 14892617407737473178396011)
  ·
    refine ⟨22338926111606209767594017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14892617407737473178396011 22338926111606209767594017)
    ·
      refine ⟨16754194583704657325695513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22338926111606209767594017 16754194583704657325695513)
      ·
        refine ⟨12565645937778492994271635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16754194583704657325695513 12565645937778492994271635)
        ·
          refine ⟨18848468906667739491407453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12565645937778492994271635 18848468906667739491407453)
          ·
            refine ⟨7068175840000402309277795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18848468906667739491407453 7068175840000402309277795)
            ·
              refine ⟨10602263760000603463916693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068175840000402309277795 10602263760000603463916693)
              ·
                refine ⟨496981113750028287371095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10602263760000603463916693 496981113750028287371095)
                ·
                  refine ⟨745471670625042431056643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496981113750028287371095 745471670625042431056643)
                  ·
                    refine ⟨1118207505937563646584965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 745471670625042431056643 1118207505937563646584965)
                    ·
                      refine ⟨209663907363293183734681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1118207505937563646584965 209663907363293183734681)
                      ·
                        rfl

theorem cell23_408319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 1, 1, 4].length) (baseStart_408319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408319 prefixEnd_408319 := by exact prefixLift 408319
  have htrace : WordTrace (prefixWord ++ tailWord_408319) baseStart_408319 baseEnd_408319 := by
    simpa [prefixWord, tailWord_408319, baseEnd_408319] using wordTrace_append hprefix tailTrace_408319
  have hstable : (prefixWord ++ tailWord_408319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408319).length < 2 ^ (prefixWord ++ tailWord_408319).sum := by decide
  have hdescent : baseEnd_408319 < baseStart_408319 := by decide
  rcases family_descends (prefixWord ++ tailWord_408319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408332 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_408332 : Nat := 118140960795 + 408332 * 2 ^ 59
def prefixEnd_408332 : Nat := 4983230072969 + 3 ^ 40 * 408332 * 2
def baseEnd_408332 : Nat := 209670582611801632872121

theorem tailTrace_408332 : CollatzResearch.WordTrace tailWord_408332 prefixEnd_408332 209670582611801632872121 := by
  unfold tailWord_408332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446545778345188199309625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9928727704460250932412833 7446545778345188199309625)
  ·
    refine ⟨5584909333758891149482219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7446545778345188199309625 5584909333758891149482219)
    ·
      refine ⟨8377364000638336724223329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5584909333758891149482219 8377364000638336724223329)
      ·
        refine ⟨6283023000478752543167497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8377364000638336724223329 6283023000478752543167497)
        ·
          refine ⟨4712267250359064407375623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6283023000478752543167497 4712267250359064407375623)
          ·
            refine ⟨7068400875538596611063435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712267250359064407375623 7068400875538596611063435)
            ·
              refine ⟨10602601313307894916595153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7068400875538596611063435 10602601313307894916595153)
              ·
                refine ⟨7951950984980921187446365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10602601313307894916595153 7951950984980921187446365)
                ·
                  refine ⟨2981981619367845445292387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7951950984980921187446365 2981981619367845445292387)
                  ·
                    refine ⟨4472972429051768167938581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2981981619367845445292387 4472972429051768167938581)
                    ·
                      refine ⟨209670582611801632872121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4472972429051768167938581 209670582611801632872121)
                      ·
                        rfl

theorem cell23_408332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_408332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408332 prefixEnd_408332 := by exact prefixLift 408332
  have htrace : WordTrace (prefixWord ++ tailWord_408332) baseStart_408332 baseEnd_408332 := by
    simpa [prefixWord, tailWord_408332, baseEnd_408332] using wordTrace_append hprefix tailTrace_408332
  have hstable : (prefixWord ++ tailWord_408332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408332).length < 2 ^ (prefixWord ++ tailWord_408332).sum := by decide
  have hdescent : baseEnd_408332 < baseStart_408332 := by decide
  rcases family_descends (prefixWord ++ tailWord_408332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408353 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_408353 : Nat := 118140960795 + 408353 * 2 ^ 59
def prefixEnd_408353 : Nat := 4983230072969 + 3 ^ 40 * 408353 * 2
def baseEnd_408353 : Nat := 209681365705546050709525

theorem tailTrace_408353 : CollatzResearch.WordTrace tailWord_408353 prefixEnd_408353 209681365705546050709525 := by
  unfold tailWord_408353
  simp only [CollatzResearch.WordTrace]
  refine ⟨14893857489614296985133713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9929238326409531323422475 14893857489614296985133713)
  ·
    refine ⟨11170393117210722738850285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14893857489614296985133713 11170393117210722738850285)
    ·
      refine ⟨4188897418954021027068857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11170393117210722738850285 4188897418954021027068857)
      ·
        refine ⟨3141673064215515770301643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4188897418954021027068857 3141673064215515770301643)
        ·
          refine ⟨4712509596323273655452465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141673064215515770301643 4712509596323273655452465)
          ·
            refine ⟨3534382197242455241589349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712509596323273655452465 3534382197242455241589349)
            ·
              refine ⟨662696661982960357798003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3534382197242455241589349 662696661982960357798003)
              ·
                refine ⟨994044992974440536697005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662696661982960357798003 994044992974440536697005)
                ·
                  refine ⟨372766872365415201261377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994044992974440536697005 372766872365415201261377)
                  ·
                    refine ⟨279575154274061400946033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 372766872365415201261377 279575154274061400946033)
                    ·
                      refine ⟨209681365705546050709525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279575154274061400946033 209681365705546050709525)
                      ·
                        rfl

theorem cell23_408353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_408353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408353 prefixEnd_408353 := by exact prefixLift 408353
  have htrace : WordTrace (prefixWord ++ tailWord_408353) baseStart_408353 baseEnd_408353 := by
    simpa [prefixWord, tailWord_408353, baseEnd_408353] using wordTrace_append hprefix tailTrace_408353
  have hstable : (prefixWord ++ tailWord_408353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408353).length < 2 ^ (prefixWord ++ tailWord_408353).sum := by decide
  have hdescent : baseEnd_408353 < baseStart_408353 := by decide
  rcases family_descends (prefixWord ++ tailWord_408353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408356 : List Nat := [2, 3, 1, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_408356 : Nat := 118140960795 + 408356 * 2 ^ 59
def prefixEnd_408356 : Nat := 4983230072969 + 3 ^ 40 * 408356 * 2
def baseEnd_408356 : Nat := 209682906147509538972011

theorem tailTrace_408356 : CollatzResearch.WordTrace tailWord_408356 prefixEnd_408356 209682906147509538972011 := by
  unfold tailWord_408356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7446983454301714248746461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9929311272402285664995281 7446983454301714248746461)
  ·
    refine ⟨2792618795363142843279923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7446983454301714248746461 2792618795363142843279923)
    ·
      refine ⟨4188928193044714264919885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2792618795363142843279923 4188928193044714264919885)
      ·
        refine ⟨1570848072391767849344957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4188928193044714264919885 1570848072391767849344957)
        ·
          refine ⟨589068027146912943504359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1570848072391767849344957 589068027146912943504359)
          ·
            refine ⟨883602040720369415256539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589068027146912943504359 883602040720369415256539)
            ·
              refine ⟨1325403061080554122884809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883602040720369415256539 1325403061080554122884809)
              ·
                refine ⟨994052295810415592163607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1325403061080554122884809 994052295810415592163607)
                ·
                  refine ⟨1491078443715623388245411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994052295810415592163607 1491078443715623388245411)
                  ·
                    refine ⟨2236617665573435082368117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491078443715623388245411 2236617665573435082368117)
                    ·
                      refine ⟨209682906147509538972011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2236617665573435082368117 209682906147509538972011)
                      ·
                        rfl

theorem cell23_408356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_408356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408356 prefixEnd_408356 := by exact prefixLift 408356
  have htrace : WordTrace (prefixWord ++ tailWord_408356) baseStart_408356 baseEnd_408356 := by
    simpa [prefixWord, tailWord_408356, baseEnd_408356] using wordTrace_append hprefix tailTrace_408356
  have hstable : (prefixWord ++ tailWord_408356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408356).length < 2 ^ (prefixWord ++ tailWord_408356).sum := by decide
  have hdescent : baseEnd_408356 < baseStart_408356 := by decide
  rcases family_descends (prefixWord ++ tailWord_408356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408366 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_408366 : Nat := 118140960795 + 408366 * 2 ^ 59
def prefixEnd_408366 : Nat := 4983230072969 + 3 ^ 40 * 408366 * 2
def baseEnd_408366 : Nat := 209688040954054499846965

theorem tailTrace_408366 : CollatzResearch.WordTrace tailWord_408366 prefixEnd_408366 209688040954054499846965 := by
  unfold tailWord_408366
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861791454820900025669619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9929554425711466803571301 1861791454820900025669619)
  ·
    refine ⟨2792687182231350038504429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1861791454820900025669619 2792687182231350038504429)
    ·
      refine ⟨1047257693336756264439161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2792687182231350038504429 1047257693336756264439161)
      ·
        refine ⟨785443270002567198329371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1047257693336756264439161 785443270002567198329371)
        ·
          refine ⟨1178164905003850797494057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785443270002567198329371 1178164905003850797494057)
          ·
            refine ⟨883623678752888098120543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178164905003850797494057 883623678752888098120543)
            ·
              refine ⟨1325435518129332147180815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883623678752888098120543 1325435518129332147180815)
              ·
                refine ⟨1988153277193998220771223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325435518129332147180815 1988153277193998220771223)
                ·
                  refine ⟨2982229915790997331156835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988153277193998220771223 2982229915790997331156835)
                  ·
                    refine ⟨4473344873686495996735253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2982229915790997331156835 4473344873686495996735253)
                    ·
                      refine ⟨209688040954054499846965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4473344873686495996735253 209688040954054499846965)
                      ·
                        rfl

theorem cell23_408366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_408366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408366 prefixEnd_408366 := by exact prefixLift 408366
  have htrace : WordTrace (prefixWord ++ tailWord_408366) baseStart_408366 baseEnd_408366 := by
    simpa [prefixWord, tailWord_408366, baseEnd_408366] using wordTrace_append hprefix tailTrace_408366
  have hstable : (prefixWord ++ tailWord_408366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408366).length < 2 ^ (prefixWord ++ tailWord_408366).sum := by decide
  have hdescent : baseEnd_408366 < baseStart_408366 := by decide
  rcases family_descends (prefixWord ++ tailWord_408366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408373 : List Nat := [1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_408373 : Nat := 118140960795 + 408373 * 2 ^ 59
def prefixEnd_408373 : Nat := 4983230072969 + 3 ^ 40 * 408373 * 2
def baseEnd_408373 : Nat := 209691635318635972459433

theorem tailTrace_408373 : CollatzResearch.WordTrace tailWord_408373 prefixEnd_408373 209691635318635972459433 := by
  unfold tailWord_408373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14894586949541840400861773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9929724633027893600574515 14894586949541840400861773)
  ·
    refine ⟨5585470106078190150323165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14894586949541840400861773 5585470106078190150323165)
    ·
      refine ⟨2094551289779321306371187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5585470106078190150323165 2094551289779321306371187)
      ·
        refine ⟨3141826934668981959556781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094551289779321306371187 3141826934668981959556781)
        ·
          refine ⟨1178185100500868234833793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3141826934668981959556781 1178185100500868234833793)
          ·
            refine ⟨883638825375651176125345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178185100500868234833793 883638825375651176125345)
            ·
              refine ⟨662729119031738382094009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883638825375651176125345 662729119031738382094009)
              ·
                refine ⟨497046839273803786570507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 662729119031738382094009 497046839273803786570507)
                ·
                  refine ⟨745570258910705679855761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497046839273803786570507 745570258910705679855761)
                  ·
                    refine ⟨559177694183029259891821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 745570258910705679855761 559177694183029259891821)
                    ·
                      refine ⟨209691635318635972459433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559177694183029259891821 209691635318635972459433)
                      ·
                        rfl

theorem cell23_408373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_408373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408373 prefixEnd_408373 := by exact prefixLift 408373
  have htrace : WordTrace (prefixWord ++ tailWord_408373) baseStart_408373 baseEnd_408373 := by
    simpa [prefixWord, tailWord_408373, baseEnd_408373] using wordTrace_append hprefix tailTrace_408373
  have hstable : (prefixWord ++ tailWord_408373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408373).length < 2 ^ (prefixWord ++ tailWord_408373).sum := by decide
  have hdescent : baseEnd_408373 < baseStart_408373 := by decide
  rcases family_descends (prefixWord ++ tailWord_408373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408390 : List Nat := [6, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5]
def baseStart_408390 : Nat := 118140960795 + 408390 * 2 ^ 59
def prefixEnd_408390 : Nat := 4983230072969 + 3 ^ 40 * 408390 * 2
def baseEnd_408390 : Nat := 209700364489762405946855

theorem tailTrace_408390 : CollatzResearch.WordTrace tailWord_408390 prefixEnd_408390 209700364489762405946855 := by
  unfold tailWord_408390
  simp only [CollatzResearch.WordTrace]
  refine ⟨465475218452507884507207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9930137993653501536153749 465475218452507884507207)
  ·
    refine ⟨698212827678761826760811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 465475218452507884507207 698212827678761826760811)
    ·
      refine ⟨1047319241518142740141217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698212827678761826760811 1047319241518142740141217)
      ·
        refine ⟨785489431138607055105913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1047319241518142740141217 785489431138607055105913)
        ·
          refine ⟨589117073353955291329435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785489431138607055105913 589117073353955291329435)
          ·
            refine ⟨883675610030932936994153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589117073353955291329435 883675610030932936994153)
            ·
              refine ⟨662756707523199702745615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 883675610030932936994153 662756707523199702745615)
              ·
                refine ⟨994135061284799554118423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 662756707523199702745615 994135061284799554118423)
                ·
                  refine ⟨1491202591927199331177635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994135061284799554118423 1491202591927199331177635)
                  ·
                    refine ⟨2236803887890798996766453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1491202591927199331177635 2236803887890798996766453)
                    ·
                      refine ⟨209700364489762405946855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2236803887890798996766453 209700364489762405946855)
                      ·
                        rfl

theorem cell23_408390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_408390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408390 prefixEnd_408390 := by exact prefixLift 408390
  have htrace : WordTrace (prefixWord ++ tailWord_408390) baseStart_408390 baseEnd_408390 := by
    simpa [prefixWord, tailWord_408390, baseEnd_408390] using wordTrace_append hprefix tailTrace_408390
  have hstable : (prefixWord ++ tailWord_408390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408390).length < 2 ^ (prefixWord ++ tailWord_408390).sum := by decide
  have hdescent : baseEnd_408390 < baseStart_408390 := by decide
  rcases family_descends (prefixWord ++ tailWord_408390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408404 : List Nat := [2, 4, 1, 1, 4, 1, 3, 2, 1, 2, 2]
def baseStart_408404 : Nat := 118140960795 + 408404 * 2 ^ 59
def prefixEnd_408404 : Nat := 4983230072969 + 3 ^ 40 * 408404 * 2
def baseEnd_408404 : Nat := 209707553218925351171791

theorem tailTrace_408404 : CollatzResearch.WordTrace tailWord_408404 prefixEnd_408404 209707553218925351171791 := by
  unfold tailWord_408404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447858806214766347620133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9930478408286355130160177 7447858806214766347620133)
  ·
    refine ⟨1396473526165268690178775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7447858806214766347620133 1396473526165268690178775)
    ·
      refine ⟨2094710289247903035268163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1396473526165268690178775 2094710289247903035268163)
      ·
        refine ⟨3142065433871854552902245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2094710289247903035268163 3142065433871854552902245)
        ·
          refine ⟨589137268850972728669171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3142065433871854552902245 589137268850972728669171)
          ·
            refine ⟨883705903276459093003757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589137268850972728669171 883705903276459093003757)
            ·
              refine ⟨331389713728672159876409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883705903276459093003757 331389713728672159876409)
              ·
                refine ⟨248542285296504119907307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331389713728672159876409 248542285296504119907307)
                ·
                  refine ⟨372813427944756179860961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248542285296504119907307 372813427944756179860961)
                  ·
                    refine ⟨279610070958567134895721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 372813427944756179860961 279610070958567134895721)
                    ·
                      refine ⟨209707553218925351171791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279610070958567134895721 209707553218925351171791)
                      ·
                        rfl

theorem cell23_408404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_408404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408404 prefixEnd_408404 := by exact prefixLift 408404
  have htrace : WordTrace (prefixWord ++ tailWord_408404) baseStart_408404 baseEnd_408404 := by
    simpa [prefixWord, tailWord_408404, baseEnd_408404] using wordTrace_append hprefix tailTrace_408404
  have hstable : (prefixWord ++ tailWord_408404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408404).length < 2 ^ (prefixWord ++ tailWord_408404).sum := by decide
  have hdescent : baseEnd_408404 < baseStart_408404 := by decide
  rcases family_descends (prefixWord ++ tailWord_408404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408420 : List Nat := [2, 3, 1, 1, 4, 1, 4, 1, 2, 1, 3]
def baseStart_408420 : Nat := 118140960795 + 408420 * 2 ^ 59
def prefixEnd_408420 : Nat := 4983230072969 + 3 ^ 40 * 408420 * 2
def baseEnd_408420 : Nat := 209715768909397288571717

theorem tailTrace_408420 : CollatzResearch.WordTrace tailWord_408420 prefixEnd_408420 209715768909397288571717 := by
  unfold tailWord_408420
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448150590185783713911357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9930867453581044951881809 7448150590185783713911357)
  ·
    refine ⟨2793056471319668892716759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7448150590185783713911357 2793056471319668892716759)
    ·
      refine ⟨4189584706979503339075139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793056471319668892716759 4189584706979503339075139)
      ·
        refine ⟨6284377060469255008612709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189584706979503339075139 6284377060469255008612709)
        ·
          refine ⟨1178320698837985314114883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6284377060469255008612709 1178320698837985314114883)
          ·
            refine ⟨1767481048256977971172325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178320698837985314114883 1767481048256977971172325)
            ·
              refine ⟨331402696548183369594811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1767481048256977971172325 331402696548183369594811)
              ·
                refine ⟨497104044822275054392217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331402696548183369594811 497104044822275054392217)
                ·
                  refine ⟨372828033616706290794163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497104044822275054392217 372828033616706290794163)
                  ·
                    refine ⟨559242050425059436191245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 372828033616706290794163 559242050425059436191245)
                    ·
                      refine ⟨209715768909397288571717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559242050425059436191245 209715768909397288571717)
                      ·
                        rfl

theorem cell23_408420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 4, 1, 2, 1, 3].length) (baseStart_408420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408420 prefixEnd_408420 := by exact prefixLift 408420
  have htrace : WordTrace (prefixWord ++ tailWord_408420) baseStart_408420 baseEnd_408420 := by
    simpa [prefixWord, tailWord_408420, baseEnd_408420] using wordTrace_append hprefix tailTrace_408420
  have hstable : (prefixWord ++ tailWord_408420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408420).length < 2 ^ (prefixWord ++ tailWord_408420).sum := by decide
  have hdescent : baseEnd_408420 < baseStart_408420 := by decide
  rcases family_descends (prefixWord ++ tailWord_408420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408430 : List Nat := [4, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_408430 : Nat := 118140960795 + 408430 * 2 ^ 59
def prefixEnd_408430 : Nat := 4983230072969 + 3 ^ 40 * 408430 * 2
def baseEnd_408430 : Nat := 209720903715942249446671

theorem tailTrace_408430 : CollatzResearch.WordTrace tailWord_408430 prefixEnd_408430 209720903715942249446671 := by
  unfold tailWord_408430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862083238791917391960843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9931110606890226090457829 1862083238791917391960843)
  ·
    refine ⟨2793124858187876087941265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1862083238791917391960843 2793124858187876087941265)
    ·
      refine ⟨2094843643640907065955949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2793124858187876087941265 2094843643640907065955949)
      ·
        refine ⟨785566366365340149733481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2094843643640907065955949 785566366365340149733481)
        ·
          refine ⟨589174774774005112300111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785566366365340149733481 589174774774005112300111)
          ·
            refine ⟨883762162161007668450167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589174774774005112300111 883762162161007668450167)
            ·
              refine ⟨1325643243241511502675251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883762162161007668450167 1325643243241511502675251)
              ·
                refine ⟨1988464864862267254012877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325643243241511502675251 1988464864862267254012877)
                ·
                  refine ⟨745674324323350220254829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1988464864862267254012877 745674324323350220254829)
                  ·
                    refine ⟨279627871621256332595561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 745674324323350220254829 279627871621256332595561)
                    ·
                      refine ⟨209720903715942249446671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279627871621256332595561 209720903715942249446671)
                      ·
                        rfl

theorem cell23_408430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_408430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408430 prefixEnd_408430 := by exact prefixLift 408430
  have htrace : WordTrace (prefixWord ++ tailWord_408430) baseStart_408430 baseEnd_408430 := by
    simpa [prefixWord, tailWord_408430, baseEnd_408430] using wordTrace_append hprefix tailTrace_408430
  have hstable : (prefixWord ++ tailWord_408430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408430).length < 2 ^ (prefixWord ++ tailWord_408430).sum := by decide
  have hdescent : baseEnd_408430 < baseStart_408430 := by decide
  rcases family_descends (prefixWord ++ tailWord_408430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408470 : List Nat := [5, 3, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_408470 : Nat := 118140960795 + 408470 * 2 ^ 59
def prefixEnd_408470 : Nat := 4983230072969 + 3 ^ 40 * 408470 * 2
def baseEnd_408470 : Nat := 69913814314040697648829

theorem tailTrace_408470 : CollatzResearch.WordTrace tailWord_408470 prefixEnd_408470 69913814314040697648829 := by
  unfold tailWord_408470
  simp only [CollatzResearch.WordTrace]
  refine ⟨931132801886901622946429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9932083220126950644761909 931132801886901622946429)
  ·
    refine ⟨349174800707588108604911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 931132801886901622946429 349174800707588108604911)
    ·
      refine ⟨523762201061382162907367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349174800707588108604911 523762201061382162907367)
      ·
        refine ⟨785643301592073244361051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523762201061382162907367 785643301592073244361051)
        ·
          refine ⟨1178464952388109866541577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785643301592073244361051 1178464952388109866541577)
          ·
            refine ⟨883848714291082399906183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178464952388109866541577 883848714291082399906183)
            ·
              refine ⟨1325773071436623599859275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 883848714291082399906183 1325773071436623599859275)
              ·
                refine ⟨1988659607154935399788913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325773071436623599859275 1988659607154935399788913)
                ·
                  refine ⟨1491494705366201549841685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1988659607154935399788913 1491494705366201549841685)
                  ·
                    refine ⟨69913814314040697648829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1491494705366201549841685 69913814314040697648829)
                    ·
                      rfl

theorem cell23_408470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_408470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408470 prefixEnd_408470 := by exact prefixLift 408470
  have htrace : WordTrace (prefixWord ++ tailWord_408470) baseStart_408470 baseEnd_408470 := by
    simpa [prefixWord, tailWord_408470, baseEnd_408470] using wordTrace_append hprefix tailTrace_408470
  have hstable : (prefixWord ++ tailWord_408470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408470).length < 2 ^ (prefixWord ++ tailWord_408470).sum := by decide
  have hdescent : baseEnd_408470 < baseStart_408470 := by decide
  rcases family_descends (prefixWord ++ tailWord_408470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408500 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 5]
def baseStart_408500 : Nat := 118140960795 + 408500 * 2 ^ 59
def prefixEnd_408500 : Nat := 4983230072969 + 3 ^ 40 * 408500 * 2
def baseEnd_408500 : Nat := 23306316373528552841261

theorem tailTrace_408500 : CollatzResearch.WordTrace tailWord_408500 prefixEnd_408500 23306316373528552841261 := by
  unfold tailWord_408500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7449609510040870545367477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9932812680054494060489969 7449609510040870545367477)
  ·
    refine ⟨698400891566331613628201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7449609510040870545367477 698400891566331613628201)
    ·
      refine ⟨523800668674748710221151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 698400891566331613628201 523800668674748710221151)
      ·
        refine ⟨785701003012123065331727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523800668674748710221151 785701003012123065331727)
        ·
          refine ⟨1178551504518184597997591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785701003012123065331727 1178551504518184597997591)
          ·
            refine ⟨1767827256777276896996387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178551504518184597997591 1767827256777276896996387)
            ·
              refine ⟨2651740885165915345494581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767827256777276896996387 2651740885165915345494581)
              ·
                refine ⟨248600707984304563640117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2651740885165915345494581 248600707984304563640117)
                ·
                  refine ⟨23306316373528552841261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 248600707984304563640117 23306316373528552841261)
                  ·
                    rfl

theorem cell23_408500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_408500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408500 prefixEnd_408500 := by exact prefixLift 408500
  have htrace : WordTrace (prefixWord ++ tailWord_408500) baseStart_408500 baseEnd_408500 := by
    simpa [prefixWord, tailWord_408500, baseEnd_408500] using wordTrace_append hprefix tailTrace_408500
  have hstable : (prefixWord ++ tailWord_408500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408500).length < 2 ^ (prefixWord ++ tailWord_408500).sum := by decide
  have hdescent : baseEnd_408500 < baseStart_408500 := by decide
  rcases family_descends (prefixWord ++ tailWord_408500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408519 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5]
def baseStart_408519 : Nat := 118140960795 + 408519 * 2 ^ 59
def prefixEnd_408519 : Nat := 4983230072969 + 3 ^ 40 * 408519 * 2
def baseEnd_408519 : Nat := 209766603494192401233761

theorem tailTrace_408519 : CollatzResearch.WordTrace tailWord_408519 prefixEnd_408519 209766603494192401233761 := by
  unfold tailWord_408519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14899912007012907335676611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9933274671341938223784407 14899912007012907335676611)
  ·
    refine ⟨22349868010519361003514917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14899912007012907335676611 22349868010519361003514917)
    ·
      refine ⟨4190600251972380188159047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22349868010519361003514917 4190600251972380188159047)
      ·
        refine ⟨6285900377958570282238571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4190600251972380188159047 6285900377958570282238571)
        ·
          refine ⟨9428850566937855423357857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285900377958570282238571 9428850566937855423357857)
          ·
            refine ⟨7071637925203391567518393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9428850566937855423357857 7071637925203391567518393)
            ·
              refine ⟨5303728443902543675638795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7071637925203391567518393 5303728443902543675638795)
              ·
                refine ⟨7955592665853815513458193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5303728443902543675638795 7955592665853815513458193)
                ·
                  refine ⟨5966694499390361635093645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7955592665853815513458193 5966694499390361635093645)
                  ·
                    refine ⟨2237510437271385613160117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5966694499390361635093645 2237510437271385613160117)
                    ·
                      refine ⟨209766603494192401233761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2237510437271385613160117 209766603494192401233761)
                      ·
                        rfl

theorem cell23_408519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_408519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408519 prefixEnd_408519 := by exact prefixLift 408519
  have htrace : WordTrace (prefixWord ++ tailWord_408519) baseStart_408519 baseEnd_408519 := by
    simpa [prefixWord, tailWord_408519, baseEnd_408519] using wordTrace_append hprefix tailTrace_408519
  have hstable : (prefixWord ++ tailWord_408519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408519).length < 2 ^ (prefixWord ++ tailWord_408519).sum := by decide
  have hdescent : baseEnd_408519 < baseStart_408519 := by decide
  rcases family_descends (prefixWord ++ tailWord_408519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408529 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_408529 : Nat := 118140960795 + 408529 * 2 ^ 59
def prefixEnd_408529 : Nat := 4983230072969 + 3 ^ 40 * 408529 * 2
def baseEnd_408529 : Nat := 209771738300737362108715

theorem tailTrace_408529 : CollatzResearch.WordTrace tailWord_408529 prefixEnd_408529 209771738300737362108715 := by
  unfold tailWord_408529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14900276736976679043540641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9933517824651119362360427 14900276736976679043540641)
  ·
    refine ⟨11175207552732509282655481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14900276736976679043540641 11175207552732509282655481)
    ·
      refine ⟨8381405664549381961991611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11175207552732509282655481 8381405664549381961991611)
      ·
        refine ⟨12572108496824072942987417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8381405664549381961991611 12572108496824072942987417)
        ·
          refine ⟨9429081372618054707240563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12572108496824072942987417 9429081372618054707240563)
          ·
            refine ⟨14143622058927082060860845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429081372618054707240563 14143622058927082060860845)
            ·
              refine ⟨5303858272097655772822817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14143622058927082060860845 5303858272097655772822817)
              ·
                refine ⟨3977893704073241829617113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5303858272097655772822817 3977893704073241829617113)
                ·
                  refine ⟨2983420278054931372212835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3977893704073241829617113 2983420278054931372212835)
                  ·
                    refine ⟨4475130417082397058319253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2983420278054931372212835 4475130417082397058319253)
                    ·
                      refine ⟨209771738300737362108715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4475130417082397058319253 209771738300737362108715)
                      ·
                        rfl

theorem cell23_408529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_408529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408529 prefixEnd_408529 := by exact prefixLift 408529
  have htrace : WordTrace (prefixWord ++ tailWord_408529) baseStart_408529 baseEnd_408529 := by
    simpa [prefixWord, tailWord_408529, baseEnd_408529] using wordTrace_append hprefix tailTrace_408529
  have hstable : (prefixWord ++ tailWord_408529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408529).length < 2 ^ (prefixWord ++ tailWord_408529).sum := by decide
  have hdescent : baseEnd_408529 < baseStart_408529 := by decide
  rcases family_descends (prefixWord ++ tailWord_408529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408536 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_408536 : Nat := 118140960795 + 408536 * 2 ^ 59
def prefixEnd_408536 : Nat := 4983230072969 + 3 ^ 40 * 408536 * 2
def baseEnd_408536 : Nat := 209775332665318834721183

theorem tailTrace_408536 : CollatzResearch.WordTrace tailWord_408536 prefixEnd_408536 209775332665318834721183 := by
  unfold tailWord_408536
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450266023975659619522731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9933688031967546159363641 7450266023975659619522731)
  ·
    refine ⟨11175399035963489429284097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7450266023975659619522731 11175399035963489429284097)
    ·
      refine ⟨8381549276972617071963073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11175399035963489429284097 8381549276972617071963073)
      ·
        refine ⟨6286161957729462803972305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8381549276972617071963073 6286161957729462803972305)
        ·
          refine ⟨4714621468297097102979229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6286161957729462803972305 4714621468297097102979229)
          ·
            refine ⟨1767983050611411413617211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4714621468297097102979229 1767983050611411413617211)
            ·
              refine ⟨2651974575917117120425817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1767983050611411413617211 2651974575917117120425817)
              ·
                refine ⟨1988980931937837840319363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651974575917117120425817 1988980931937837840319363)
                ·
                  refine ⟨2983471397906756760479045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988980931937837840319363 2983471397906756760479045)
                  ·
                    refine ⟨559400887107516892589821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2983471397906756760479045 559400887107516892589821)
                    ·
                      refine ⟨209775332665318834721183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559400887107516892589821 209775332665318834721183)
                      ·
                        rfl

theorem cell23_408536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_408536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408536 prefixEnd_408536 := by exact prefixLift 408536
  have htrace : WordTrace (prefixWord ++ tailWord_408536) baseStart_408536 baseEnd_408536 := by
    simpa [prefixWord, tailWord_408536, baseEnd_408536] using wordTrace_append hprefix tailTrace_408536
  have hstable : (prefixWord ++ tailWord_408536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408536).length < 2 ^ (prefixWord ++ tailWord_408536).sum := by decide
  have hdescent : baseEnd_408536 < baseStart_408536 := by decide
  rcases family_descends (prefixWord ++ tailWord_408536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408564 : List Nat := [2, 6, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_408564 : Nat := 118140960795 + 408564 * 2 ^ 59
def prefixEnd_408564 : Nat := 4983230072969 + 3 ^ 40 * 408564 * 2
def baseEnd_408564 : Nat := 69929903374548241723685

theorem tailTrace_408564 : CollatzResearch.WordTrace tailWord_408564 prefixEnd_408564 69929903374548241723685 := by
  unfold tailWord_408564
  simp only [CollatzResearch.WordTrace]
  refine ⟨7450776645924940010532373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9934368861233253347376497 7450776645924940010532373)
  ·
    refine ⟨349255155277731562993705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7450776645924940010532373 349255155277731562993705)
    ·
      refine ⟨261941366458298672245279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349255155277731562993705 261941366458298672245279)
      ·
        refine ⟨392912049687448008367919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261941366458298672245279 392912049687448008367919)
        ·
          refine ⟨589368074531172012551879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392912049687448008367919 589368074531172012551879)
          ·
            refine ⟨884052111796758018827819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589368074531172012551879 884052111796758018827819)
            ·
              refine ⟨1326078167695137028241729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884052111796758018827819 1326078167695137028241729)
              ·
                refine ⟨994558625771352771181297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326078167695137028241729 994558625771352771181297)
                ·
                  refine ⟨745918969328514578385973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994558625771352771181297 745918969328514578385973)
                  ·
                    refine ⟨69929903374548241723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 745918969328514578385973 69929903374548241723685)
                    ·
                      rfl

theorem cell23_408564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_408564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408564 prefixEnd_408564 := by exact prefixLift 408564
  have htrace : WordTrace (prefixWord ++ tailWord_408564) baseStart_408564 baseEnd_408564 := by
    simpa [prefixWord, tailWord_408564, baseEnd_408564] using wordTrace_append hprefix tailTrace_408564
  have hstable : (prefixWord ++ tailWord_408564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408564).length < 2 ^ (prefixWord ++ tailWord_408564).sum := by decide
  have hdescent : baseEnd_408564 < baseStart_408564 := by decide
  rcases family_descends (prefixWord ++ tailWord_408564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408577 : List Nat := [1, 2, 4, 1, 2, 3, 3, 2, 1, 4]
def baseStart_408577 : Nat := 118140960795 + 408577 * 2 ^ 59
def prefixEnd_408577 : Nat := 4983230072969 + 3 ^ 40 * 408577 * 2
def baseEnd_408577 : Nat := 69932128457384391436165

theorem tailTrace_408577 : CollatzResearch.WordTrace tailWord_408577 prefixEnd_408577 69932128457384391436165 := by
  unfold tailWord_408577
  simp only [CollatzResearch.WordTrace]
  refine ⟨14902027440802783241287985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9934684960535188827525323 14902027440802783241287985)
  ·
    refine ⟨11176520580602087430965989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14902027440802783241287985 11176520580602087430965989)
    ·
      refine ⟨2095597608862891393306123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11176520580602087430965989 2095597608862891393306123)
      ·
        refine ⟨3143396413294337089959185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095597608862891393306123 3143396413294337089959185)
        ·
          refine ⟨2357547309970752817469389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143396413294337089959185 2357547309970752817469389)
          ·
            refine ⟨884080241239032306551021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2357547309970752817469389 884080241239032306551021)
            ·
              refine ⟨331530090464637114956633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884080241239032306551021 331530090464637114956633)
              ·
                refine ⟨248647567848477836217475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331530090464637114956633 248647567848477836217475)
                ·
                  refine ⟨372971351772716754326213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248647567848477836217475 372971351772716754326213)
                  ·
                    refine ⟨69932128457384391436165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 372971351772716754326213 69932128457384391436165)
                    ·
                      rfl

theorem cell23_408577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_408577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408577 prefixEnd_408577 := by exact prefixLift 408577
  have htrace : WordTrace (prefixWord ++ tailWord_408577) baseStart_408577 baseEnd_408577 := by
    simpa [prefixWord, tailWord_408577, baseEnd_408577] using wordTrace_append hprefix tailTrace_408577
  have hstable : (prefixWord ++ tailWord_408577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408577).length < 2 ^ (prefixWord ++ tailWord_408577).sum := by decide
  have hdescent : baseEnd_408577 < baseStart_408577 := by decide
  rcases family_descends (prefixWord ++ tailWord_408577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408579 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7]
def baseStart_408579 : Nat := 118140960795 + 408579 * 2 ^ 59
def prefixEnd_408579 : Nat := 4983230072969 + 3 ^ 40 * 408579 * 2
def baseEnd_408579 : Nat := 209797412333462166483485

theorem tailTrace_408579 : CollatzResearch.WordTrace tailWord_408579 prefixEnd_408579 209797412333462166483485 := by
  unfold tailWord_408579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14902100386795537582860791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9934733591197025055240527 14902100386795537582860791)
  ·
    refine ⟨22353150580193306374291187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14902100386795537582860791 22353150580193306374291187)
    ·
      refine ⟨33529725870289959561436781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22353150580193306374291187 33529725870289959561436781)
      ·
        refine ⟨12573647201358734835538793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33529725870289959561436781 12573647201358734835538793)
        ·
          refine ⟨9430235401019051126654095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12573647201358734835538793 9430235401019051126654095)
          ·
            refine ⟨14145353101528576689981143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9430235401019051126654095 14145353101528576689981143)
            ·
              refine ⟨21218029652292865034971715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14145353101528576689981143 21218029652292865034971715)
              ·
                refine ⟨31827044478439297552457573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21218029652292865034971715 31827044478439297552457573)
                ·
                  refine ⟨5967570839707368291085795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31827044478439297552457573 5967570839707368291085795)
                  ·
                    refine ⟨8951356259561052436628693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5967570839707368291085795 8951356259561052436628693)
                    ·
                      refine ⟨209797412333462166483485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8951356259561052436628693 209797412333462166483485)
                      ·
                        rfl

theorem cell23_408579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_408579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408579 prefixEnd_408579 := by exact prefixLift 408579
  have htrace : WordTrace (prefixWord ++ tailWord_408579) baseStart_408579 baseEnd_408579 := by
    simpa [prefixWord, tailWord_408579, baseEnd_408579] using wordTrace_append hprefix tailTrace_408579
  have hstable : (prefixWord ++ tailWord_408579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408579).length < 2 ^ (prefixWord ++ tailWord_408579).sum := by decide
  have hdescent : baseEnd_408579 < baseStart_408579 := by decide
  rcases family_descends (prefixWord ++ tailWord_408579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408590 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 6]
def baseStart_408590 : Nat := 118140960795 + 408590 * 2 ^ 59
def prefixEnd_408590 : Nat := 4983230072969 + 3 ^ 40 * 408590 * 2
def baseEnd_408590 : Nat := 23311451180073513716215

theorem tailTrace_408590 : CollatzResearch.WordTrace tailWord_408590 prefixEnd_408590 23311451180073513716215 := by
  unfold tailWord_408590
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862812698719460807688903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9935001059837124307674149 1862812698719460807688903)
  ·
    refine ⟨2794219048079191211533355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1862812698719460807688903 2794219048079191211533355)
    ·
      refine ⟨4191328572118786817300033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2794219048079191211533355 4191328572118786817300033)
      ·
        refine ⟨3143496429089090112975025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4191328572118786817300033 3143496429089090112975025)
        ·
          refine ⟨2357622321816817584731269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3143496429089090112975025 2357622321816817584731269)
          ·
            refine ⟨442054185340653297137113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2357622321816817584731269 442054185340653297137113)
            ·
              refine ⟨331540639005489972852835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442054185340653297137113 331540639005489972852835)
              ·
                refine ⟨497310958508234959279253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331540639005489972852835 497310958508234959279253)
                ·
                  refine ⟨23311451180073513716215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 497310958508234959279253 23311451180073513716215)
                  ·
                    rfl

theorem cell23_408590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 6].length) (baseStart_408590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408590 prefixEnd_408590 := by exact prefixLift 408590
  have htrace : WordTrace (prefixWord ++ tailWord_408590) baseStart_408590 baseEnd_408590 := by
    simpa [prefixWord, tailWord_408590, baseEnd_408590] using wordTrace_append hprefix tailTrace_408590
  have hstable : (prefixWord ++ tailWord_408590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408590).length < 2 ^ (prefixWord ++ tailWord_408590).sum := by decide
  have hdescent : baseEnd_408590 < baseStart_408590 := by decide
  rcases family_descends (prefixWord ++ tailWord_408590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408610 : List Nat := [3, 3, 1, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_408610 : Nat := 118140960795 + 408610 * 2 ^ 59
def prefixEnd_408610 : Nat := 4983230072969 + 3 ^ 40 * 408610 * 2
def baseEnd_408610 : Nat := 209813330233751545195843

theorem tailTrace_408610 : CollatzResearch.WordTrace tailWord_408610 prefixEnd_408610 209813330233751545195843 := by
  unfold tailWord_408610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725807762420807469309821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9935487366455486584826189 3725807762420807469309821)
  ·
    refine ⟨1397177910907802800991183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3725807762420807469309821 1397177910907802800991183)
    ·
      refine ⟨2095766866361704201486775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397177910907802800991183 2095766866361704201486775)
      ·
        refine ⟨3143650299542556302230163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095766866361704201486775 3143650299542556302230163)
        ·
          refine ⟨4715475449313834453345245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143650299542556302230163 4715475449313834453345245)
          ·
            refine ⟨1768303293492687920004467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4715475449313834453345245 1768303293492687920004467)
            ·
              refine ⟨2652454940239031880006701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768303293492687920004467 2652454940239031880006701)
              ·
                refine ⟨994670602589636955002513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2652454940239031880006701 994670602589636955002513)
                ·
                  refine ⟨746002951942227716251885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 994670602589636955002513 746002951942227716251885)
                  ·
                    refine ⟨279751106978335393594457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746002951942227716251885 279751106978335393594457)
                    ·
                      refine ⟨209813330233751545195843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279751106978335393594457 209813330233751545195843)
                      ·
                        rfl

theorem cell23_408610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_408610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408610 prefixEnd_408610 := by exact prefixLift 408610
  have htrace : WordTrace (prefixWord ++ tailWord_408610) baseStart_408610 baseEnd_408610 := by
    simpa [prefixWord, tailWord_408610, baseEnd_408610] using wordTrace_append hprefix tailTrace_408610
  have hstable : (prefixWord ++ tailWord_408610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408610).length < 2 ^ (prefixWord ++ tailWord_408610).sum := by decide
  have hdescent : baseEnd_408610 < baseStart_408610 := by decide
  rcases family_descends (prefixWord ++ tailWord_408610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408640 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2]
def baseStart_408640 : Nat := 118140960795 + 408640 * 2 ^ 59
def prefixEnd_408640 : Nat := 4983230072969 + 3 ^ 40 * 408640 * 2
def baseEnd_408640 : Nat := 209828734653386427820705

theorem tailTrace_408640 : CollatzResearch.WordTrace tailWord_408640 prefixEnd_408640 209828734653386427820705 := by
  unfold tailWord_408640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452162619787272500415687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9936216826383030000554249 7452162619787272500415687)
  ·
    refine ⟨11178243929680908750623531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452162619787272500415687 11178243929680908750623531)
    ·
      refine ⟨16767365894521363125935297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178243929680908750623531 16767365894521363125935297)
      ·
        refine ⟨12575524420891022344451473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16767365894521363125935297 12575524420891022344451473)
        ·
          refine ⟨9431643315668266758338605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12575524420891022344451473 9431643315668266758338605)
          ·
            refine ⟨3536866243375600034376977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9431643315668266758338605 3536866243375600034376977)
            ·
              refine ⟨2652649682531700025782733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536866243375600034376977 2652649682531700025782733)
              ·
                refine ⟨994743630949387509668525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2652649682531700025782733 994743630949387509668525)
                ·
                  refine ⟨373028861606020316125697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 994743630949387509668525 373028861606020316125697)
                  ·
                    refine ⟨279771646204515237094273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373028861606020316125697 279771646204515237094273)
                    ·
                      refine ⟨209828734653386427820705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279771646204515237094273 209828734653386427820705)
                      ·
                        rfl

theorem cell23_408640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 3, 2, 2].length) (baseStart_408640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408640 prefixEnd_408640 := by exact prefixLift 408640
  have htrace : WordTrace (prefixWord ++ tailWord_408640) baseStart_408640 baseEnd_408640 := by
    simpa [prefixWord, tailWord_408640, baseEnd_408640] using wordTrace_append hprefix tailTrace_408640
  have hstable : (prefixWord ++ tailWord_408640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408640).length < 2 ^ (prefixWord ++ tailWord_408640).sum := by decide
  have hdescent : baseEnd_408640 < baseStart_408640 := by decide
  rcases family_descends (prefixWord ++ tailWord_408640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408673 : List Nat := [1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_408673 : Nat := 118140960795 + 408673 * 2 ^ 59
def prefixEnd_408673 : Nat := 4983230072969 + 3 ^ 40 * 408673 * 2
def baseEnd_408673 : Nat := 209845679514984798708053

theorem tailTrace_408673 : CollatzResearch.WordTrace tailWord_408673 prefixEnd_408673 209845679514984798708053 := by
  unfold tailWord_408673
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905528848454991636782673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9937019232303327757855115 14905528848454991636782673)
  ·
    refine ⟨11179146636341243727587005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14905528848454991636782673 11179146636341243727587005)
    ·
      refine ⟨4192179988627966397845127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11179146636341243727587005 4192179988627966397845127)
      ·
        refine ⟨6288269982941949596767691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4192179988627966397845127 6288269982941949596767691)
        ·
          refine ⟨9432404974412924395151537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288269982941949596767691 9432404974412924395151537)
          ·
            refine ⟨7074303730809693296363653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9432404974412924395151537 7074303730809693296363653)
            ·
              refine ⟨1326431949526817493068185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7074303730809693296363653 1326431949526817493068185)
              ·
                refine ⟨994823962145113119801139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326431949526817493068185 994823962145113119801139)
                ·
                  refine ⟨1492235943217669679701709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 994823962145113119801139 1492235943217669679701709)
                  ·
                    refine ⟨559588478706626129888141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1492235943217669679701709 559588478706626129888141)
                    ·
                      refine ⟨209845679514984798708053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559588478706626129888141 209845679514984798708053)
                      ·
                        rfl

theorem cell23_408673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_408673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408673 prefixEnd_408673 := by exact prefixLift 408673
  have htrace : WordTrace (prefixWord ++ tailWord_408673) baseStart_408673 baseEnd_408673 := by
    simpa [prefixWord, tailWord_408673, baseEnd_408673] using wordTrace_append hprefix tailTrace_408673
  have hstable : (prefixWord ++ tailWord_408673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408673).length < 2 ^ (prefixWord ++ tailWord_408673).sum := by decide
  have hdescent : baseEnd_408673 < baseStart_408673 := by decide
  rcases family_descends (prefixWord ++ tailWord_408673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408674 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_408674 : Nat := 118140960795 + 408674 * 2 ^ 59
def prefixEnd_408674 : Nat := 4983230072969 + 3 ^ 40 * 408674 * 2
def baseEnd_408674 : Nat := 209846192995639294795549

theorem tailTrace_408674 : CollatzResearch.WordTrace tailWord_408674 prefixEnd_408674 209846192995639294795549 := by
  unfold tailWord_408674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726391330362842201892269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9937043547634245871712717 3726391330362842201892269)
  ·
    refine ⟨1397396748886065825709601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3726391330362842201892269 1397396748886065825709601)
    ·
      refine ⟨1048047561664549369282201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1397396748886065825709601 1048047561664549369282201)
      ·
        refine ⟨786035671248412026961651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048047561664549369282201 786035671248412026961651)
        ·
          refine ⟨1179053506872618040442477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786035671248412026961651 1179053506872618040442477)
          ·
            refine ⟨442145065077231765165929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1179053506872618040442477 442145065077231765165929)
            ·
              refine ⟨331608798807923823874447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442145065077231765165929 331608798807923823874447)
              ·
                refine ⟨497413198211885735811671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331608798807923823874447 497413198211885735811671)
                ·
                  refine ⟨746119797317828603717507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497413198211885735811671 746119797317828603717507)
                  ·
                    refine ⟨1119179695976742905576261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 746119797317828603717507 1119179695976742905576261)
                    ·
                      refine ⟨209846192995639294795549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1119179695976742905576261 209846192995639294795549)
                      ·
                        rfl

theorem cell23_408674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_408674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408674 prefixEnd_408674 := by exact prefixLift 408674
  have htrace : WordTrace (prefixWord ++ tailWord_408674) baseStart_408674 baseEnd_408674 := by
    simpa [prefixWord, tailWord_408674, baseEnd_408674] using wordTrace_append hprefix tailTrace_408674
  have hstable : (prefixWord ++ tailWord_408674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408674).length < 2 ^ (prefixWord ++ tailWord_408674).sum := by decide
  have hdescent : baseEnd_408674 < baseStart_408674 := by decide
  rcases family_descends (prefixWord ++ tailWord_408674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408690 : List Nat := [3, 2, 1, 2, 2, 1, 3, 1, 4, 1, 3]
def baseStart_408690 : Nat := 118140960795 + 408690 * 2 ^ 59
def prefixEnd_408690 : Nat := 4983230072969 + 3 ^ 40 * 408690 * 2
def baseEnd_408690 : Nat := 209854408686111232195475

theorem tailTrace_408690 : CollatzResearch.WordTrace tailWord_408690 prefixEnd_408690 209854408686111232195475 := by
  unfold tailWord_408690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726537222348350885037881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9937432592928935693434349 3726537222348350885037881)
  ·
    refine ⟨2794902916761263163778411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3726537222348350885037881 2794902916761263163778411)
    ·
      refine ⟨4192354375141894745667617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2794902916761263163778411 4192354375141894745667617)
      ·
        refine ⟨3144265781356421059250713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192354375141894745667617 3144265781356421059250713)
        ·
          refine ⟨2358199336017315794438035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144265781356421059250713 2358199336017315794438035)
          ·
            refine ⟨3537299004025973691657053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358199336017315794438035 3537299004025973691657053)
            ·
              refine ⟨1326487126509740134371395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3537299004025973691657053 1326487126509740134371395)
              ·
                refine ⟨1989730689764610201557093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326487126509740134371395 1989730689764610201557093)
                ·
                  refine ⟨373074504330864412791955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989730689764610201557093 373074504330864412791955)
                  ·
                    refine ⟨559611756496296619187933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 373074504330864412791955 559611756496296619187933)
                    ·
                      refine ⟨209854408686111232195475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559611756496296619187933 209854408686111232195475)
                      ·
                        rfl

theorem cell23_408690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_408690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408690 prefixEnd_408690 := by exact prefixLift 408690
  have htrace : WordTrace (prefixWord ++ tailWord_408690) baseStart_408690 baseEnd_408690 := by
    simpa [prefixWord, tailWord_408690, baseEnd_408690] using wordTrace_append hprefix tailTrace_408690
  have hstable : (prefixWord ++ tailWord_408690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408690).length < 2 ^ (prefixWord ++ tailWord_408690).sum := by decide
  have hdescent : baseEnd_408690 < baseStart_408690 := by decide
  rcases family_descends (prefixWord ++ tailWord_408690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408696 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_408696 : Nat := 118140960795 + 408696 * 2 ^ 59
def prefixEnd_408696 : Nat := 4983230072969 + 3 ^ 40 * 408696 * 2
def baseEnd_408696 : Nat := 209857489570038208720447

theorem tailTrace_408696 : CollatzResearch.WordTrace tailWord_408696 prefixEnd_408696 209857489570038208720447 := by
  unfold tailWord_408696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453183863685833282434971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9937578484914444376579961 7453183863685833282434971)
  ·
    refine ⟨11179775795528749923652457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7453183863685833282434971 11179775795528749923652457)
    ·
      refine ⟨8384831846646562442739343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11179775795528749923652457 8384831846646562442739343)
      ·
        refine ⟨12577247769969843664109015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8384831846646562442739343 12577247769969843664109015)
        ·
          refine ⟨18865871654954765496163523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12577247769969843664109015 18865871654954765496163523)
          ·
            refine ⟨28298807482432148244245285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18865871654954765496163523 28298807482432148244245285)
            ·
              refine ⟨5306026402956027795795991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28298807482432148244245285 5306026402956027795795991)
              ·
                refine ⟨7959039604434041693693987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306026402956027795795991 7959039604434041693693987)
                ·
                  refine ⟨11938559406651062540540981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959039604434041693693987 11938559406651062540540981)
                  ·
                    refine ⟨1119239944373537113175717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11938559406651062540540981 1119239944373537113175717)
                    ·
                      refine ⟨209857489570038208720447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1119239944373537113175717 209857489570038208720447)
                      ·
                        rfl

theorem cell23_408696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_408696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408696 prefixEnd_408696 := by exact prefixLift 408696
  have htrace : WordTrace (prefixWord ++ tailWord_408696) baseStart_408696 baseEnd_408696 := by
    simpa [prefixWord, tailWord_408696, baseEnd_408696] using wordTrace_append hprefix tailTrace_408696
  have hstable : (prefixWord ++ tailWord_408696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408696).length < 2 ^ (prefixWord ++ tailWord_408696).sum := by decide
  have hdescent : baseEnd_408696 < baseStart_408696 := by decide
  rcases family_descends (prefixWord ++ tailWord_408696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408707 : List Nat := [1, 1, 1, 3, 3, 2, 5, 1, 2, 1, 3]
def baseStart_408707 : Nat := 118140960795 + 408707 * 2 ^ 59
def prefixEnd_408707 : Nat := 4983230072969 + 3 ^ 40 * 408707 * 2
def baseEnd_408707 : Nat := 209863137857237665682897

theorem tailTrace_408707 : CollatzResearch.WordTrace tailWord_408707 prefixEnd_408707 209863137857237665682897 := by
  unfold tailWord_408707
  simp only [CollatzResearch.WordTrace]
  refine ⟨14906768930331815443520375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9937845953554543629013583 14906768930331815443520375)
  ·
    refine ⟨22360153395497723165280563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14906768930331815443520375 22360153395497723165280563)
    ·
      refine ⟨33540230093246584747920845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22360153395497723165280563 33540230093246584747920845)
      ·
        refine ⟨12577586284967469280470317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33540230093246584747920845 12577586284967469280470317)
        ·
          refine ⟨4716594856862800980176369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12577586284967469280470317 4716594856862800980176369)
          ·
            refine ⟨3537446142647100735132277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716594856862800980176369 3537446142647100735132277)
            ·
              refine ⟨331635575873165693918651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3537446142647100735132277 331635575873165693918651)
              ·
                refine ⟨497453363809748540877977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331635575873165693918651 497453363809748540877977)
                ·
                  refine ⟨373090022857311405658483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497453363809748540877977 373090022857311405658483)
                  ·
                    refine ⟨559635034285967108487725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 373090022857311405658483 559635034285967108487725)
                    ·
                      refine ⟨209863137857237665682897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559635034285967108487725 209863137857237665682897)
                      ·
                        rfl

theorem cell23_408707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_408707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408707 prefixEnd_408707 := by exact prefixLift 408707
  have htrace : WordTrace (prefixWord ++ tailWord_408707) baseStart_408707 baseEnd_408707 := by
    simpa [prefixWord, tailWord_408707, baseEnd_408707] using wordTrace_append hprefix tailTrace_408707
  have hstable : (prefixWord ++ tailWord_408707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408707).length < 2 ^ (prefixWord ++ tailWord_408707).sum := by decide
  have hdescent : baseEnd_408707 < baseStart_408707 := by decide
  rcases family_descends (prefixWord ++ tailWord_408707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408716 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_408716 : Nat := 118140960795 + 408716 * 2 ^ 59
def prefixEnd_408716 : Nat := 4983230072969 + 3 ^ 40 * 408716 * 2
def baseEnd_408716 : Nat := 209867759183128130470355

theorem tailTrace_408716 : CollatzResearch.WordTrace tailWord_408716 prefixEnd_408716 209867759183128130470355 := by
  unfold tailWord_408716
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453548593649604990299001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9938064791532806653732001 7453548593649604990299001)
  ·
    refine ⟨5590161445237203742724251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7453548593649604990299001 5590161445237203742724251)
    ·
      refine ⟨8385242167855805614086377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590161445237203742724251 8385242167855805614086377)
      ·
        refine ⟨6288931625891854210564783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385242167855805614086377 6288931625891854210564783)
        ·
          refine ⟨9433397438837781315847175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288931625891854210564783 9433397438837781315847175)
          ·
            refine ⟨14150096158256671973770763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9433397438837781315847175 14150096158256671973770763)
            ·
              refine ⟨21225144237385007960656145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14150096158256671973770763 21225144237385007960656145)
              ·
                refine ⟨15918858178038755970492109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21225144237385007960656145 15918858178038755970492109)
                ·
                  refine ⟨5969571816764533488934541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15918858178038755970492109 5969571816764533488934541)
                  ·
                    refine ⟨2238589431286700058350453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5969571816764533488934541 2238589431286700058350453)
                    ·
                      refine ⟨209867759183128130470355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2238589431286700058350453 209867759183128130470355)
                      ·
                        rfl

theorem cell23_408716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_408716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408716 prefixEnd_408716 := by exact prefixLift 408716
  have htrace : WordTrace (prefixWord ++ tailWord_408716) baseStart_408716 baseEnd_408716 := by
    simpa [prefixWord, tailWord_408716, baseEnd_408716] using wordTrace_append hprefix tailTrace_408716
  have hstable : (prefixWord ++ tailWord_408716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408716).length < 2 ^ (prefixWord ++ tailWord_408716).sum := by decide
  have hdescent : baseEnd_408716 < baseStart_408716 := by decide
  rcases family_descends (prefixWord ++ tailWord_408716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408733 : List Nat := [1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_408733 : Nat := 118140960795 + 408733 * 2 ^ 59
def prefixEnd_408733 : Nat := 4983230072969 + 3 ^ 40 * 408733 * 2
def baseEnd_408733 : Nat := 209876488354254563957777

theorem tailTrace_408733 : CollatzResearch.WordTrace tailWord_408733 prefixEnd_408733 209876488354254563957777 := by
  unfold tailWord_408733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14907717228237621883966853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9938478152158414589311235 14907717228237621883966853)
  ·
    refine ⟨2795196980294554103243785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14907717228237621883966853 2795196980294554103243785)
    ·
      refine ⟨2096397735220915577432839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2795196980294554103243785 2096397735220915577432839)
      ·
        refine ⟨3144596602831373366149259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096397735220915577432839 3144596602831373366149259)
        ·
          refine ⟨4716894904247060049223889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144596602831373366149259 4716894904247060049223889)
          ·
            refine ⟨3537671178185295036917917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716894904247060049223889 3537671178185295036917917)
            ·
              refine ⟨1326626691819485638844219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3537671178185295036917917 1326626691819485638844219)
              ·
                refine ⟨1989940037729228458266329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1326626691819485638844219 1989940037729228458266329)
                ·
                  refine ⟨1492455028296921343699747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1989940037729228458266329 1492455028296921343699747)
                  ·
                    refine ⟨2238682542445382015549621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1492455028296921343699747 2238682542445382015549621)
                    ·
                      refine ⟨209876488354254563957777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2238682542445382015549621 209876488354254563957777)
                      ·
                        rfl

theorem cell23_408733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_408733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408733 prefixEnd_408733 := by exact prefixLift 408733
  have htrace : WordTrace (prefixWord ++ tailWord_408733) baseStart_408733 baseEnd_408733 := by
    simpa [prefixWord, tailWord_408733, baseEnd_408733] using wordTrace_append hprefix tailTrace_408733
  have hstable : (prefixWord ++ tailWord_408733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408733).length < 2 ^ (prefixWord ++ tailWord_408733).sum := by decide
  have hdescent : baseEnd_408733 < baseStart_408733 := by decide
  rcases family_descends (prefixWord ++ tailWord_408733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408734 : List Nat := [4, 3, 1, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_408734 : Nat := 118140960795 + 408734 * 2 ^ 59
def prefixEnd_408734 : Nat := 4983230072969 + 3 ^ 40 * 408734 * 2
def baseEnd_408734 : Nat := 209877001834909060045273

theorem tailTrace_408734 : CollatzResearch.WordTrace tailWord_408734 prefixEnd_408734 209877001834909060045273 := by
  unfold tailWord_408734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863469212654249881844157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9938502467489332703168837 1863469212654249881844157)
  ·
    refine ⟨698800954745343705691559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1863469212654249881844157 698800954745343705691559)
    ·
      refine ⟨1048201432118015558537339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698800954745343705691559 1048201432118015558537339)
      ·
        refine ⟨1572302148177023337806009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048201432118015558537339 1572302148177023337806009)
        ·
          refine ⟨1179226611132767503354507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572302148177023337806009 1179226611132767503354507)
          ·
            refine ⟨1768839916699151255031761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179226611132767503354507 1768839916699151255031761)
            ·
              refine ⟨1326629937524363441273821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1768839916699151255031761 1326629937524363441273821)
              ·
                refine ⟨497486226571636290477683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326629937524363441273821 497486226571636290477683)
                ·
                  refine ⟨746229339857454435716525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497486226571636290477683 746229339857454435716525)
                  ·
                    refine ⟨279836002446545413393697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 746229339857454435716525 279836002446545413393697)
                    ·
                      refine ⟨209877001834909060045273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279836002446545413393697 209877001834909060045273)
                      ·
                        rfl

theorem cell23_408734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_408734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408734 prefixEnd_408734 := by exact prefixLift 408734
  have htrace : WordTrace (prefixWord ++ tailWord_408734) baseStart_408734 baseEnd_408734 := by
    simpa [prefixWord, tailWord_408734, baseEnd_408734] using wordTrace_append hprefix tailTrace_408734
  have hstable : (prefixWord ++ tailWord_408734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408734).length < 2 ^ (prefixWord ++ tailWord_408734).sum := by decide
  have hdescent : baseEnd_408734 < baseStart_408734 := by decide
  rcases family_descends (prefixWord ++ tailWord_408734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408764 : List Nat := [2, 2, 2, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_408764 : Nat := 118140960795 + 408764 * 2 ^ 59
def prefixEnd_408764 : Nat := 4983230072969 + 3 ^ 40 * 408764 * 2
def baseEnd_408764 : Nat := 209892406254543942670135

theorem tailTrace_408764 : CollatzResearch.WordTrace tailWord_408764 prefixEnd_408764 209892406254543942670135 := by
  unfold tailWord_408764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7454423945562657089172673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9939231927416876118896897 7454423945562657089172673)
  ·
    refine ⟨5590817959171992816879505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7454423945562657089172673 5590817959171992816879505)
    ·
      refine ⟨4193113469378994612659629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5590817959171992816879505 4193113469378994612659629)
      ·
        refine ⟨1572417551017122979747361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4193113469378994612659629 1572417551017122979747361)
        ·
          refine ⟨1179313163262842234810521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1572417551017122979747361 1179313163262842234810521)
          ·
            refine ⟨884484872447131676107891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1179313163262842234810521 884484872447131676107891)
            ·
              refine ⟨1326727308670697514161837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884484872447131676107891 1326727308670697514161837)
              ·
                refine ⟨497522740751511567810689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1326727308670697514161837 497522740751511567810689)
                ·
                  refine ⟨373142055563633675858017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497522740751511567810689 373142055563633675858017)
                  ·
                    refine ⟨279856541672725256893513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373142055563633675858017 279856541672725256893513)
                    ·
                      refine ⟨209892406254543942670135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279856541672725256893513 209892406254543942670135)
                      ·
                        rfl

theorem cell23_408764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_408764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408764 prefixEnd_408764 := by exact prefixLift 408764
  have htrace : WordTrace (prefixWord ++ tailWord_408764) baseStart_408764 baseEnd_408764 := by
    simpa [prefixWord, tailWord_408764, baseEnd_408764] using wordTrace_append hprefix tailTrace_408764
  have hstable : (prefixWord ++ tailWord_408764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408764).length < 2 ^ (prefixWord ++ tailWord_408764).sum := by decide
  have hdescent : baseEnd_408764 < baseStart_408764 := by decide
  rcases family_descends (prefixWord ++ tailWord_408764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408781 : List Nat := [1, 6, 2, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_408781 : Nat := 118140960795 + 408781 * 2 ^ 59
def prefixEnd_408781 : Nat := 4983230072969 + 3 ^ 40 * 408781 * 2
def baseEnd_408781 : Nat := 209901135425670376157557

theorem tailTrace_408781 : CollatzResearch.WordTrace tailWord_408781 prefixEnd_408781 209901135425670376157557 := by
  unfold tailWord_408781
  simp only [CollatzResearch.WordTrace]
  refine ⟨14909467932063726081714197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9939645288042484054476131 14909467932063726081714197)
  ·
    refine ⟨698881309315487160080353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14909467932063726081714197 698881309315487160080353)
    ·
      refine ⟨524160981986615370060265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 698881309315487160080353 524160981986615370060265)
      ·
        refine ⟨393120736489961527545199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524160981986615370060265 393120736489961527545199)
        ·
          refine ⟨589681104734942291317799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393120736489961527545199 589681104734942291317799)
          ·
            refine ⟨884521657102413436976699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589681104734942291317799 884521657102413436976699)
            ·
              refine ⟨1326782485653620155465049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 884521657102413436976699 1326782485653620155465049)
              ·
                refine ⟨995086864240215116598787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1326782485653620155465049 995086864240215116598787)
                ·
                  refine ⟨1492630296360322674898181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995086864240215116598787 1492630296360322674898181)
                  ·
                    refine ⟨279868180567560501543409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1492630296360322674898181 279868180567560501543409)
                    ·
                      refine ⟨209901135425670376157557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279868180567560501543409 209901135425670376157557)
                      ·
                        rfl

theorem cell23_408781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_408781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408781 prefixEnd_408781 := by exact prefixLift 408781
  have htrace : WordTrace (prefixWord ++ tailWord_408781) baseStart_408781 baseEnd_408781 := by
    simpa [prefixWord, tailWord_408781, baseEnd_408781] using wordTrace_append hprefix tailTrace_408781
  have hstable : (prefixWord ++ tailWord_408781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408781).length < 2 ^ (prefixWord ++ tailWord_408781).sum := by decide
  have hdescent : baseEnd_408781 < baseStart_408781 := by decide
  rcases family_descends (prefixWord ++ tailWord_408781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408823 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3]
def baseStart_408823 : Nat := 118140960795 + 408823 * 2 ^ 59
def prefixEnd_408823 : Nat := 4983230072969 + 3 ^ 40 * 408823 * 2
def baseEnd_408823 : Nat := 209922701613159211832363

theorem tailTrace_408823 : CollatzResearch.WordTrace tailWord_408823 prefixEnd_408823 209922701613159211832363 := by
  unfold tailWord_408823
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910999797911567254743123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9940666531941044836495415 14910999797911567254743123)
  ·
    refine ⟨22366499696867350882114685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14910999797911567254743123 22366499696867350882114685)
    ·
      refine ⟨8387437386325256580793007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22366499696867350882114685 8387437386325256580793007)
      ·
        refine ⟨12581156079487884871189511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8387437386325256580793007 12581156079487884871189511)
        ·
          refine ⟨18871734119231827306784267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12581156079487884871189511 18871734119231827306784267)
          ·
            refine ⟨28307601178847740960176401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18871734119231827306784267 28307601178847740960176401)
            ·
              refine ⟨21230700884135805720132301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28307601178847740960176401 21230700884135805720132301)
              ·
                refine ⟨7961512831550927145049613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21230700884135805720132301 7961512831550927145049613)
                ·
                  refine ⟨2985567311831597679393605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7961512831550927145049613 2985567311831597679393605)
                  ·
                    refine ⟨559793870968424564886301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2985567311831597679393605 559793870968424564886301)
                    ·
                      refine ⟨209922701613159211832363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 559793870968424564886301 209922701613159211832363)
                      ·
                        rfl

theorem cell23_408823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_408823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408823 prefixEnd_408823 := by exact prefixLift 408823
  have htrace : WordTrace (prefixWord ++ tailWord_408823) baseStart_408823 baseEnd_408823 := by
    simpa [prefixWord, tailWord_408823, baseEnd_408823] using wordTrace_append hprefix tailTrace_408823
  have hstable : (prefixWord ++ tailWord_408823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408823).length < 2 ^ (prefixWord ++ tailWord_408823).sum := by decide
  have hdescent : baseEnd_408823 < baseStart_408823 := by decide
  rcases family_descends (prefixWord ++ tailWord_408823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408834 : List Nat := [3, 4, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_408834 : Nat := 118140960795 + 408834 * 2 ^ 59
def prefixEnd_408834 : Nat := 4983230072969 + 3 ^ 40 * 408834 * 2
def baseEnd_408834 : Nat := 69976116633452889598271

theorem tailTrace_408834 : CollatzResearch.WordTrace tailWord_408834 prefixEnd_408834 69976116633452889598271 := by
  unfold tailWord_408834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727850250217929033348389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9940934000581144088929037 3727850250217929033348389)
  ·
    refine ⟨698971921915861693752823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3727850250217929033348389 698971921915861693752823)
    ·
      refine ⟨1048457882873792540629235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698971921915861693752823 1048457882873792540629235)
      ·
        refine ⟨1572686824310688810943853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048457882873792540629235 1572686824310688810943853)
        ·
          refine ⟨589757559116508304103945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1572686824310688810943853 589757559116508304103945)
          ·
            refine ⟨442318169337381228077959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589757559116508304103945 442318169337381228077959)
            ·
              refine ⟨663477254006071842116939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442318169337381228077959 663477254006071842116939)
              ·
                refine ⟨995215881009107763175409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663477254006071842116939 995215881009107763175409)
                ·
                  refine ⟨746411910756830822381557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995215881009107763175409 746411910756830822381557)
                  ·
                    refine ⟨69976116633452889598271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 746411910756830822381557 69976116633452889598271)
                    ·
                      rfl

theorem cell23_408834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_408834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408834 prefixEnd_408834 := by exact prefixLift 408834
  have htrace : WordTrace (prefixWord ++ tailWord_408834) baseStart_408834 baseEnd_408834 := by
    simpa [prefixWord, tailWord_408834, baseEnd_408834] using wordTrace_append hprefix tailTrace_408834
  have hstable : (prefixWord ++ tailWord_408834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408834).length < 2 ^ (prefixWord ++ tailWord_408834).sum := by decide
  have hdescent : baseEnd_408834 < baseStart_408834 := by decide
  rcases family_descends (prefixWord ++ tailWord_408834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408860 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 6]
def baseStart_408860 : Nat := 118140960795 + 408860 * 2 ^ 59
def prefixEnd_408860 : Nat := 4983230072969 + 3 ^ 40 * 408860 * 2
def baseEnd_408860 : Nat := 23326855599708396341077

theorem tailTrace_408860 : CollatzResearch.WordTrace tailWord_408860 prefixEnd_408860 23326855599708396341077 := by
  unfold tailWord_408860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456174649388761286920017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9941566199185015049226689 7456174649388761286920017)
  ·
    refine ⟨5592130987041570965190013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7456174649388761286920017 5592130987041570965190013)
    ·
      refine ⟨2097049120140589111946255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5592130987041570965190013 2097049120140589111946255)
      ·
        refine ⟨3145573680210883667919383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097049120140589111946255 3145573680210883667919383)
        ·
          refine ⟨4718360520316325501879075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145573680210883667919383 4718360520316325501879075)
          ·
            refine ⟨7077540780474488252818613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718360520316325501879075 7077540780474488252818613)
            ·
              refine ⟨663519448169483273701745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7077540780474488252818613 663519448169483273701745)
              ·
                refine ⟨497639586127112455276309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663519448169483273701745 497639586127112455276309)
                ·
                  refine ⟨23326855599708396341077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 497639586127112455276309 23326855599708396341077)
                  ·
                    rfl

theorem cell23_408860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_408860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408860 prefixEnd_408860 := by exact prefixLift 408860
  have htrace : WordTrace (prefixWord ++ tailWord_408860) baseStart_408860 baseEnd_408860 := by
    simpa [prefixWord, tailWord_408860, baseEnd_408860] using wordTrace_append hprefix tailTrace_408860
  have hstable : (prefixWord ++ tailWord_408860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408860).length < 2 ^ (prefixWord ++ tailWord_408860).sum := by decide
  have hdescent : baseEnd_408860 < baseStart_408860 := by decide
  rcases family_descends (prefixWord ++ tailWord_408860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408880 : List Nat := [2, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2]
def baseStart_408880 : Nat := 118140960795 + 408880 * 2 ^ 59
def prefixEnd_408880 : Nat := 4983230072969 + 3 ^ 40 * 408880 * 2
def baseEnd_408880 : Nat := 209951970010465488819601

theorem tailTrace_408880 : CollatzResearch.WordTrace tailWord_408880 prefixEnd_408880 209951970010465488819601 := by
  unfold tailWord_408880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456539379352532994784047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9942052505803377326378729 7456539379352532994784047)
  ·
    refine ⟨11184809069028799492176071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456539379352532994784047 11184809069028799492176071)
    ·
      refine ⟨16777213603543199238264107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11184809069028799492176071 16777213603543199238264107)
      ·
        refine ⟨25165820405314798857396161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16777213603543199238264107 25165820405314798857396161)
        ·
          refine ⟨18874365303986099143047121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25165820405314798857396161 18874365303986099143047121)
          ·
            refine ⟨14155773977989574357285341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18874365303986099143047121 14155773977989574357285341)
            ·
              refine ⟨5308415241746090383982003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14155773977989574357285341 5308415241746090383982003)
              ·
                refine ⟨7962622862619135575973005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308415241746090383982003 7962622862619135575973005)
                ·
                  refine ⟨2985983573482175840989877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7962622862619135575973005 2985983573482175840989877)
                  ·
                    refine ⟨279935960013953985092801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2985983573482175840989877 279935960013953985092801)
                    ·
                      refine ⟨209951970010465488819601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 279935960013953985092801 209951970010465488819601)
                      ·
                        rfl

theorem cell23_408880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 3, 5, 2].length) (baseStart_408880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408880 prefixEnd_408880 := by exact prefixLift 408880
  have htrace : WordTrace (prefixWord ++ tailWord_408880) baseStart_408880 baseEnd_408880 := by
    simpa [prefixWord, tailWord_408880, baseEnd_408880] using wordTrace_append hprefix tailTrace_408880
  have hstable : (prefixWord ++ tailWord_408880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408880).length < 2 ^ (prefixWord ++ tailWord_408880).sum := by decide
  have hdescent : baseEnd_408880 < baseStart_408880 := by decide
  rcases family_descends (prefixWord ++ tailWord_408880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408920 : List Nat := [2, 1, 2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_408920 : Nat := 118140960795 + 408920 * 2 ^ 59
def prefixEnd_408920 : Nat := 4983230072969 + 3 ^ 40 * 408920 * 2
def baseEnd_408920 : Nat := 69990836412215110773139

theorem tailTrace_408920 : CollatzResearch.WordTrace tailWord_408920 prefixEnd_408920 69990836412215110773139 := by
  unfold tailWord_408920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457268839280076410512107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9943025119040101880682809 7457268839280076410512107)
  ·
    refine ⟨11185903258920114615768161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7457268839280076410512107 11185903258920114615768161)
    ·
      refine ⟨8389427444190085961826121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11185903258920114615768161 8389427444190085961826121)
      ·
        refine ⟨6292070583142564471369591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8389427444190085961826121 6292070583142564471369591)
        ·
          refine ⟨9438105874713846707054387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292070583142564471369591 9438105874713846707054387)
          ·
            refine ⟨14157158812070770060581581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438105874713846707054387 14157158812070770060581581)
            ·
              refine ⟨5308934554526538772718093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14157158812070770060581581 5308934554526538772718093)
              ·
                refine ⟨1990850457947452039769285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5308934554526538772718093 1990850457947452039769285)
                ·
                  refine ⟨373284460865147257456741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990850457947452039769285 373284460865147257456741)
                  ·
                    refine ⟨69990836412215110773139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373284460865147257456741 69990836412215110773139)
                    ·
                      rfl

theorem cell23_408920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_408920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408920 prefixEnd_408920 := by exact prefixLift 408920
  have htrace : WordTrace (prefixWord ++ tailWord_408920) baseStart_408920 baseEnd_408920 := by
    simpa [prefixWord, tailWord_408920, baseEnd_408920] using wordTrace_append hprefix tailTrace_408920
  have hstable : (prefixWord ++ tailWord_408920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408920).length < 2 ^ (prefixWord ++ tailWord_408920).sum := by decide
  have hdescent : baseEnd_408920 < baseStart_408920 := by decide
  rcases family_descends (prefixWord ++ tailWord_408920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408940 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_408940 : Nat := 118140960795 + 408940 * 2 ^ 59
def prefixEnd_408940 : Nat := 4983230072969 + 3 ^ 40 * 408940 * 2
def baseEnd_408940 : Nat := 209982778849735254069325

theorem tailTrace_408940 : CollatzResearch.WordTrace tailWord_408940 prefixEnd_408940 209982778849735254069325 := by
  unfold tailWord_408940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457633569243848118376137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9943511425658464157834849 7457633569243848118376137)
  ·
    refine ⟨5593225176932886088782103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7457633569243848118376137 5593225176932886088782103)
    ·
      refine ⟨8389837765399329133173155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5593225176932886088782103 8389837765399329133173155)
      ·
        refine ⟨12584756648098993699759733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8389837765399329133173155 12584756648098993699759733)
        ·
          refine ⟨1179820935759280659352475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12584756648098993699759733 1179820935759280659352475)
          ·
            refine ⟨1769731403638920989028713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1179820935759280659352475 1769731403638920989028713)
            ·
              refine ⟨1327298552729190741771535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1769731403638920989028713 1327298552729190741771535)
              ·
                refine ⟨1990947829093786112657303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1327298552729190741771535 1990947829093786112657303)
                ·
                  refine ⟨2986421743640679168985955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990947829093786112657303 2986421743640679168985955)
                  ·
                    refine ⟨4479632615461018753478933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2986421743640679168985955 4479632615461018753478933)
                    ·
                      refine ⟨209982778849735254069325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4479632615461018753478933 209982778849735254069325)
                      ·
                        rfl

theorem cell23_408940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_408940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408940 prefixEnd_408940 := by exact prefixLift 408940
  have htrace : WordTrace (prefixWord ++ tailWord_408940) baseStart_408940 baseEnd_408940 := by
    simpa [prefixWord, tailWord_408940, baseEnd_408940] using wordTrace_append hprefix tailTrace_408940
  have hstable : (prefixWord ++ tailWord_408940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408940).length < 2 ^ (prefixWord ++ tailWord_408940).sum := by decide
  have hdescent : baseEnd_408940 < baseStart_408940 := by decide
  rcases family_descends (prefixWord ++ tailWord_408940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408958 : List Nat := [4, 2, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_408958 : Nat := 118140960795 + 408958 * 2 ^ 59
def prefixEnd_408958 : Nat := 4983230072969 + 3 ^ 40 * 408958 * 2
def baseEnd_408958 : Nat := 69997340500505394548081

theorem tailTrace_408958 : CollatzResearch.WordTrace tailWord_408958 prefixEnd_408958 69997340500505394548081 := by
  unfold tailWord_408958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1864490456552810663863441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9943949101614990207271685 1864490456552810663863441)
  ·
    refine ⟨1398367842414607997897581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1864490456552810663863441 1398367842414607997897581)
    ·
      refine ⟨524387940905477999211593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1398367842414607997897581 524387940905477999211593)
      ·
        refine ⟨393290955679108499408695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 524387940905477999211593 393290955679108499408695)
        ·
          refine ⟨589936433518662749113043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393290955679108499408695 589936433518662749113043)
          ·
            refine ⟨884904650277994123669565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589936433518662749113043 884904650277994123669565)
            ·
              refine ⟨331839243854247796376087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884904650277994123669565 331839243854247796376087)
              ·
                refine ⟨497758865781371694564131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331839243854247796376087 497758865781371694564131)
                ·
                  refine ⟨746638298672057541846197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497758865781371694564131 746638298672057541846197)
                  ·
                    refine ⟨69997340500505394548081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 746638298672057541846197 69997340500505394548081)
                    ·
                      rfl

theorem cell23_408958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_408958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408958 prefixEnd_408958 := by exact prefixLift 408958
  have htrace : WordTrace (prefixWord ++ tailWord_408958) baseStart_408958 baseEnd_408958 := by
    simpa [prefixWord, tailWord_408958, baseEnd_408958] using wordTrace_append hprefix tailTrace_408958
  have hstable : (prefixWord ++ tailWord_408958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408958).length < 2 ^ (prefixWord ++ tailWord_408958).sum := by decide
  have hdescent : baseEnd_408958 < baseStart_408958 := by decide
  rcases family_descends (prefixWord ++ tailWord_408958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408961 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_408961 : Nat := 118140960795 + 408961 * 2 ^ 59
def prefixEnd_408961 : Nat := 4983230072969 + 3 ^ 40 * 408961 * 2
def baseEnd_408961 : Nat := 209993561943479671906729

theorem tailTrace_408961 : CollatzResearch.WordTrace tailWord_408961 prefixEnd_408961 209993561943479671906729 := by
  unfold tailWord_408961
  simp only [CollatzResearch.WordTrace]
  refine ⟨14916033071411616823266737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9944022047607744548844491 14916033071411616823266737)
  ·
    refine ⟨11187024803558712617450053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14916033071411616823266737 11187024803558712617450053)
    ·
      refine ⟨2097567150667258615771885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11187024803558712617450053 2097567150667258615771885)
      ·
        refine ⟨786587681500221980914457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2097567150667258615771885 786587681500221980914457)
        ·
          refine ⟨589940761125166485685843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786587681500221980914457 589940761125166485685843)
          ·
            refine ⟨884911141687749728528765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589940761125166485685843 884911141687749728528765)
            ·
              refine ⟨331841678132906148198287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884911141687749728528765 331841678132906148198287)
              ·
                refine ⟨497762517199359222297431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331841678132906148198287 497762517199359222297431)
                ·
                  refine ⟨746643775799038833446147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497762517199359222297431 746643775799038833446147)
                  ·
                    refine ⟨1119965663698558250169221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 746643775799038833446147 1119965663698558250169221)
                    ·
                      refine ⟨209993561943479671906729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1119965663698558250169221 209993561943479671906729)
                      ·
                        rfl

theorem cell23_408961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_408961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408961 prefixEnd_408961 := by exact prefixLift 408961
  have htrace : WordTrace (prefixWord ++ tailWord_408961) baseStart_408961 baseEnd_408961 := by
    simpa [prefixWord, tailWord_408961, baseEnd_408961] using wordTrace_append hprefix tailTrace_408961
  have hstable : (prefixWord ++ tailWord_408961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408961).length < 2 ^ (prefixWord ++ tailWord_408961).sum := by decide
  have hdescent : baseEnd_408961 < baseStart_408961 := by decide
  rcases family_descends (prefixWord ++ tailWord_408961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408984 : List Nat := [2, 1, 2, 5, 3, 1, 1, 8]
def baseStart_408984 : Nat := 118140960795 + 408984 * 2 ^ 59
def prefixEnd_408984 : Nat := 4983230072969 + 3 ^ 40 * 408984 * 2
def baseEnd_408984 : Nat := 7777976740686410441449

theorem tailTrace_408984 : CollatzResearch.WordTrace tailWord_408984 prefixEnd_408984 7777976740686410441449 := by
  unfold tailWord_408984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7458435975164145875677003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9944581300218861167569337 7458435975164145875677003)
  ·
    refine ⟨11187653962746218813515505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7458435975164145875677003 11187653962746218813515505)
    ·
      refine ⟨8390740472059664110136629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11187653962746218813515505 8390740472059664110136629)
      ·
        refine ⟨786631919255593510325309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8390740472059664110136629 786631919255593510325309)
        ·
          refine ⟨294986969720847566371991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 786631919255593510325309 294986969720847566371991)
          ·
            refine ⟨442480454581271349557987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294986969720847566371991 442480454581271349557987)
            ·
              refine ⟨663720681871907024336981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442480454581271349557987 663720681871907024336981)
              ·
                refine ⟨7777976740686410441449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 663720681871907024336981 7777976740686410441449)
                ·
                  rfl

theorem cell23_408984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 8].length) (baseStart_408984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408984 prefixEnd_408984 := by exact prefixLift 408984
  have htrace : WordTrace (prefixWord ++ tailWord_408984) baseStart_408984 baseEnd_408984 := by
    simpa [prefixWord, tailWord_408984, baseEnd_408984] using wordTrace_append hprefix tailTrace_408984
  have hstable : (prefixWord ++ tailWord_408984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408984).length < 2 ^ (prefixWord ++ tailWord_408984).sum := by decide
  have hdescent : baseEnd_408984 < baseStart_408984 := by decide
  rcases family_descends (prefixWord ++ tailWord_408984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408994 : List Nat := [3, 3, 1, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_408994 : Nat := 118140960795 + 408994 * 2 ^ 59
def prefixEnd_408994 : Nat := 4983230072969 + 3 ^ 40 * 408994 * 2
def baseEnd_408994 : Nat := 210010506805078042794077

theorem tailTrace_408994 : CollatzResearch.WordTrace tailWord_408994 prefixEnd_408994 210010506805078042794077 := by
  unfold tailWord_408994
  simp only [CollatzResearch.WordTrace]
  refine ⟨3729309170073015864804509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9944824453528042306145357 3729309170073015864804509)
  ·
    refine ⟨1398490938777380949301691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3729309170073015864804509 1398490938777380949301691)
    ·
      refine ⟨2097736408166071423952537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398490938777380949301691 2097736408166071423952537)
      ·
        refine ⟨1573302306124553567964403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2097736408166071423952537 1573302306124553567964403)
        ·
          refine ⟨2359953459186830351946605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573302306124553567964403 2359953459186830351946605)
          ·
            refine ⟨884982547195061381979977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2359953459186830351946605 884982547195061381979977)
            ·
              refine ⟨663736910396296036484983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884982547195061381979977 663736910396296036484983)
              ·
                refine ⟨995605365594444054727475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 663736910396296036484983 995605365594444054727475)
                ·
                  refine ⟨1493408048391666082091213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 995605365594444054727475 1493408048391666082091213)
                  ·
                    refine ⟨560028018146874780784205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1493408048391666082091213 560028018146874780784205)
                    ·
                      refine ⟨210010506805078042794077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560028018146874780784205 210010506805078042794077)
                      ·
                        rfl

theorem cell23_408994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_408994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_408994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_408994 prefixEnd_408994 := by exact prefixLift 408994
  have htrace : WordTrace (prefixWord ++ tailWord_408994) baseStart_408994 baseEnd_408994 := by
    simpa [prefixWord, tailWord_408994, baseEnd_408994] using wordTrace_append hprefix tailTrace_408994
  have hstable : (prefixWord ++ tailWord_408994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408994).length < 2 ^ (prefixWord ++ tailWord_408994).sum := by decide
  have hdescent : baseEnd_408994 < baseStart_408994 := by decide
  rcases family_descends (prefixWord ++ tailWord_408994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409028 : List Nat := [2, 3, 3, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_409028 : Nat := 118140960795 + 409028 * 2 ^ 59
def prefixEnd_409028 : Nat := 4983230072969 + 3 ^ 40 * 409028 * 2
def baseEnd_409028 : Nat := 210027965147330909768921

theorem tailTrace_409028 : CollatzResearch.WordTrace tailWord_409028 prefixEnd_409028 210027965147330909768921 := by
  unfold tailWord_409028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7459238381084443632977869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9945651174779258177303825 7459238381084443632977869)
  ·
    refine ⟨2797214392906666362366701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7459238381084443632977869 2797214392906666362366701)
    ·
      refine ⟨1048955397339999885887513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2797214392906666362366701 1048955397339999885887513)
      ·
        refine ⟨786716548004999914415635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048955397339999885887513 786716548004999914415635)
        ·
          refine ⟨1180074822007499871623453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786716548004999914415635 1180074822007499871623453)
          ·
            refine ⟨442528058252812451858795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1180074822007499871623453 442528058252812451858795)
            ·
              refine ⟨663792087379218677788193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442528058252812451858795 663792087379218677788193)
              ·
                refine ⟨497844065534414008341145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663792087379218677788193 497844065534414008341145)
                ·
                  refine ⟨373383049150810506255859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497844065534414008341145 373383049150810506255859)
                  ·
                    refine ⟨560074573726215759383789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 373383049150810506255859 560074573726215759383789)
                    ·
                      refine ⟨210027965147330909768921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560074573726215759383789 210027965147330909768921)
                      ·
                        rfl

theorem cell23_409028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_409028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409028 prefixEnd_409028 := by exact prefixLift 409028
  have htrace : WordTrace (prefixWord ++ tailWord_409028) baseStart_409028 baseEnd_409028 := by
    simpa [prefixWord, tailWord_409028, baseEnd_409028] using wordTrace_append hprefix tailTrace_409028
  have hstable : (prefixWord ++ tailWord_409028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409028).length < 2 ^ (prefixWord ++ tailWord_409028).sum := by decide
  have hdescent : baseEnd_409028 < baseStart_409028 := by decide
  rcases family_descends (prefixWord ++ tailWord_409028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409102 : List Nat := [4, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_409102 : Nat := 118140960795 + 409102 * 2 ^ 59
def prefixEnd_409102 : Nat := 4983230072969 + 3 ^ 40 * 409102 * 2
def baseEnd_409102 : Nat := 210065962715763620243581

theorem tailTrace_409102 : CollatzResearch.WordTrace tailWord_409102 prefixEnd_409102 210065962715763620243581 := by
  unfold tailWord_409102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865146970487599738018695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9947450509267198602766373 1865146970487599738018695)
  ·
    refine ⟨2797720455731399607028043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865146970487599738018695 2797720455731399607028043)
    ·
      refine ⟨4196580683597099410542065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2797720455731399607028043 4196580683597099410542065)
      ·
        refine ⟨3147435512697824557906549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4196580683597099410542065 3147435512697824557906549)
        ·
          refine ⟨295072079315421052303739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3147435512697824557906549 295072079315421052303739)
          ·
            refine ⟨442608118973131578455609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295072079315421052303739 442608118973131578455609)
            ·
              refine ⟨331956089229848683841707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442608118973131578455609 331956089229848683841707)
              ·
                refine ⟨497934133844773025762561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331956089229848683841707 497934133844773025762561)
                ·
                  refine ⟨373450600383579769321921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497934133844773025762561 373450600383579769321921)
                  ·
                    refine ⟨280087950287684826991441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373450600383579769321921 280087950287684826991441)
                    ·
                      refine ⟨210065962715763620243581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280087950287684826991441 210065962715763620243581)
                      ·
                        rfl

theorem cell23_409102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_409102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409102 prefixEnd_409102 := by exact prefixLift 409102
  have htrace : WordTrace (prefixWord ++ tailWord_409102) baseStart_409102 baseEnd_409102 := by
    simpa [prefixWord, tailWord_409102, baseEnd_409102] using wordTrace_append hprefix tailTrace_409102
  have hstable : (prefixWord ++ tailWord_409102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409102).length < 2 ^ (prefixWord ++ tailWord_409102).sum := by decide
  have hdescent : baseEnd_409102 < baseStart_409102 := by decide
  rcases family_descends (prefixWord ++ tailWord_409102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409144 : List Nat := [2, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_409144 : Nat := 118140960795 + 409144 * 2 ^ 59
def prefixEnd_409144 : Nat := 4983230072969 + 3 ^ 40 * 409144 * 2
def baseEnd_409144 : Nat := 210087528903252455918387

theorem tailTrace_409144 : CollatzResearch.WordTrace tailWord_409144 prefixEnd_409144 210087528903252455918387 := by
  unfold tailWord_409144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7461353814874319538589243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9948471753165759384785657 7461353814874319538589243)
  ·
    refine ⟨11192030722311479307883865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7461353814874319538589243 11192030722311479307883865)
    ·
      refine ⟨8394023041733609480912899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11192030722311479307883865 8394023041733609480912899)
      ·
        refine ⟨12591034562600414221369349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394023041733609480912899 12591034562600414221369349)
        ·
          refine ⟨2360818980487577666506753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12591034562600414221369349 2360818980487577666506753)
          ·
            refine ⟨1770614235365683249880065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360818980487577666506753 1770614235365683249880065)
            ·
              refine ⟨1327960676524262437410049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1770614235365683249880065 1327960676524262437410049)
              ·
                refine ⟨995970507393196828057537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1327960676524262437410049 995970507393196828057537)
                ·
                  refine ⟨746977880544897621043153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 995970507393196828057537 746977880544897621043153)
                  ·
                    refine ⟨560233410408673215782365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 746977880544897621043153 560233410408673215782365)
                    ·
                      refine ⟨210087528903252455918387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560233410408673215782365 210087528903252455918387)
                      ·
                        rfl

theorem cell23_409144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_409144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409144 prefixEnd_409144 := by exact prefixLift 409144
  have htrace : WordTrace (prefixWord ++ tailWord_409144) baseStart_409144 baseEnd_409144 := by
    simpa [prefixWord, tailWord_409144, baseEnd_409144] using wordTrace_append hprefix tailTrace_409144
  have hstable : (prefixWord ++ tailWord_409144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409144).length < 2 ^ (prefixWord ++ tailWord_409144).sum := by decide
  have hdescent : baseEnd_409144 < baseStart_409144 := by decide
  rcases family_descends (prefixWord ++ tailWord_409144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409151 : List Nat := [1, 1, 2, 2, 3, 4, 1, 4, 1, 4]
def baseStart_409151 : Nat := 118140960795 + 409151 * 2 ^ 59
def prefixEnd_409151 : Nat := 4983230072969 + 3 ^ 40 * 409151 * 2
def baseEnd_409151 : Nat := 70030374422611309510285

theorem tailTrace_409151 : CollatzResearch.WordTrace tailWord_409151 prefixEnd_409151 70030374422611309510285 := by
  unfold tailWord_409151
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922962940723279272683307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9948641960482186181788871 14922962940723279272683307)
  ·
    refine ⟨22384444411084918909024961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922962940723279272683307 22384444411084918909024961)
    ·
      refine ⟨16788333308313689181768721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22384444411084918909024961 16788333308313689181768721)
      ·
        refine ⟨12591249981235266886326541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16788333308313689181768721 12591249981235266886326541)
        ·
          refine ⟨4721718742963225082372453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12591249981235266886326541 4721718742963225082372453)
          ·
            refine ⟨885322264305604702944835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4721718742963225082372453 885322264305604702944835)
            ·
              refine ⟨1327983396458407054417253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885322264305604702944835 1327983396458407054417253)
              ·
                refine ⟨248996886835951322703235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1327983396458407054417253 248996886835951322703235)
                ·
                  refine ⟨373495330253926984054853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248996886835951322703235 373495330253926984054853)
                  ·
                    refine ⟨70030374422611309510285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373495330253926984054853 70030374422611309510285)
                    ·
                      rfl

theorem cell23_409151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 4, 1, 4].length) (baseStart_409151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409151 prefixEnd_409151 := by exact prefixLift 409151
  have htrace : WordTrace (prefixWord ++ tailWord_409151) baseStart_409151 baseEnd_409151 := by
    simpa [prefixWord, tailWord_409151, baseEnd_409151] using wordTrace_append hprefix tailTrace_409151
  have hstable : (prefixWord ++ tailWord_409151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409151).length < 2 ^ (prefixWord ++ tailWord_409151).sum := by decide
  have hdescent : baseEnd_409151 < baseStart_409151 := by decide
  rcases family_descends (prefixWord ++ tailWord_409151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409198 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_409198 : Nat := 118140960795 + 409198 * 2 ^ 59
def prefixEnd_409198 : Nat := 4983230072969 + 3 ^ 40 * 409198 * 2
def baseEnd_409198 : Nat := 23346139650955027182571

theorem tailTrace_409198 : CollatzResearch.WordTrace tailWord_409198 prefixEnd_409198 23346139650955027182571 := by
  unfold tailWord_409198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865584646444125787455531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9949784781035337533096165 1865584646444125787455531)
  ·
    refine ⟨2798376969666188681183297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1865584646444125787455531 2798376969666188681183297)
    ·
      refine ⟨2098782727249641510887473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2798376969666188681183297 2098782727249641510887473)
      ·
        refine ⟨1574087045437231133165605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098782727249641510887473 1574087045437231133165605)
        ·
          refine ⟨295141321019480837468551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1574087045437231133165605 295141321019480837468551)
          ·
            refine ⟨442711981529221256202827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295141321019480837468551 442711981529221256202827)
            ·
              refine ⟨664067972293831884304241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442711981529221256202827 664067972293831884304241)
              ·
                refine ⟨498050979220373913228181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664067972293831884304241 498050979220373913228181)
                ·
                  refine ⟨23346139650955027182571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 498050979220373913228181 23346139650955027182571)
                  ·
                    rfl

theorem cell23_409198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_409198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409198 prefixEnd_409198 := by exact prefixLift 409198
  have htrace : WordTrace (prefixWord ++ tailWord_409198) baseStart_409198 baseEnd_409198 := by
    simpa [prefixWord, tailWord_409198, baseEnd_409198] using wordTrace_append hprefix tailTrace_409198
  have hstable : (prefixWord ++ tailWord_409198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409198).length < 2 ^ (prefixWord ++ tailWord_409198).sum := by decide
  have hdescent : baseEnd_409198 < baseStart_409198 := by decide
  rcases family_descends (prefixWord ++ tailWord_409198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409227 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6]
def baseStart_409227 : Nat := 118140960795 + 409227 * 2 ^ 59
def prefixEnd_409227 : Nat := 4983230072969 + 3 ^ 40 * 409227 * 2
def baseEnd_409227 : Nat := 210130147797575631180505

theorem tailTrace_409227 : CollatzResearch.WordTrace tailWord_409227 prefixEnd_409227 210130147797575631180505 := by
  unfold tailWord_409227
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925734888447944252449935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9950489925631962834966623 14925734888447944252449935)
  ·
    refine ⟨22388602332671916378674903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14925734888447944252449935 22388602332671916378674903)
    ·
      refine ⟨33582903499007874568012355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22388602332671916378674903 33582903499007874568012355)
      ·
        refine ⟨50374355248511811852018533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33582903499007874568012355 50374355248511811852018533)
        ·
          refine ⟨9445191609095964722253475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50374355248511811852018533 9445191609095964722253475)
          ·
            refine ⟨14167787413643947083380213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445191609095964722253475 14167787413643947083380213)
            ·
              refine ⟨1328230070029120039066895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14167787413643947083380213 1328230070029120039066895)
              ·
                refine ⟨1992345105043680058600343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1328230070029120039066895 1992345105043680058600343)
                ·
                  refine ⟨2988517657565520087900515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1992345105043680058600343 2988517657565520087900515)
                  ·
                    refine ⟨4482776486348280131850773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2988517657565520087900515 4482776486348280131850773)
                    ·
                      refine ⟨210130147797575631180505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4482776486348280131850773 210130147797575631180505)
                      ·
                        rfl

theorem cell23_409227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 6].length) (baseStart_409227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409227 prefixEnd_409227 := by exact prefixLift 409227
  have htrace : WordTrace (prefixWord ++ tailWord_409227) baseStart_409227 baseEnd_409227 := by
    simpa [prefixWord, tailWord_409227, baseEnd_409227] using wordTrace_append hprefix tailTrace_409227
  have hstable : (prefixWord ++ tailWord_409227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409227).length < 2 ^ (prefixWord ++ tailWord_409227).sum := by decide
  have hdescent : baseEnd_409227 < baseStart_409227 := by decide
  rcases family_descends (prefixWord ++ tailWord_409227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409267 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 2, 7]
def baseStart_409267 : Nat := 118140960795 + 409267 * 2 ^ 59
def prefixEnd_409267 : Nat := 4983230072969 + 3 ^ 40 * 409267 * 2
def baseEnd_409267 : Nat := 70050229007918491560107

theorem tailTrace_409267 : CollatzResearch.WordTrace tailWord_409267 prefixEnd_409267 70050229007918491560107 := by
  unfold tailWord_409267
  simp only [CollatzResearch.WordTrace]
  refine ⟨14927193808303031083906055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9951462538868687389270703 14927193808303031083906055)
  ·
    refine ⟨22390790712454546625859083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14927193808303031083906055 22390790712454546625859083)
    ·
      refine ⟨33586186068681819938788625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22390790712454546625859083 33586186068681819938788625)
      ·
        refine ⟨25189639551511364954091469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33586186068681819938788625 25189639551511364954091469)
        ·
          refine ⟨9446114831816761857784301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25189639551511364954091469 9446114831816761857784301)
          ·
            refine ⟨3542293061931285696669113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9446114831816761857784301 3542293061931285696669113)
            ·
              refine ⟨2656719796448464272501835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3542293061931285696669113 2656719796448464272501835)
              ·
                refine ⟨3985079694672696408752753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2656719796448464272501835 3985079694672696408752753)
                ·
                  refine ⟨2988809771004522306564565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985079694672696408752753 2988809771004522306564565)
                  ·
                    refine ⟨70050229007918491560107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2988809771004522306564565 70050229007918491560107)
                    ·
                      rfl

theorem cell23_409267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 2, 7].length) (baseStart_409267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409267 prefixEnd_409267 := by exact prefixLift 409267
  have htrace : WordTrace (prefixWord ++ tailWord_409267) baseStart_409267 baseEnd_409267 := by
    simpa [prefixWord, tailWord_409267, baseEnd_409267] using wordTrace_append hprefix tailTrace_409267
  have hstable : (prefixWord ++ tailWord_409267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409267).length < 2 ^ (prefixWord ++ tailWord_409267).sum := by decide
  have hdescent : baseEnd_409267 < baseStart_409267 := by decide
  rcases family_descends (prefixWord ++ tailWord_409267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409302 : List Nat := [5, 2, 1, 3, 2, 1, 1, 1, 1, 1, 5]
def baseStart_409302 : Nat := 118140960795 + 409302 * 2 ^ 59
def prefixEnd_409302 : Nat := 4983230072969 + 3 ^ 40 * 409302 * 2
def baseEnd_409302 : Nat := 210168658846662837742661

theorem tailTrace_409302 : CollatzResearch.WordTrace tailWord_409302 prefixEnd_409302 210168658846662837742661 := by
  unfold tailWord_409302
  simp only [CollatzResearch.WordTrace]
  refine ⟨933029397698514503839385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9952313575450821374286773 933029397698514503839385)
  ·
    refine ⟨699772048273885877879539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 933029397698514503839385 699772048273885877879539)
    ·
      refine ⟨1049658072410828816819309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699772048273885877879539 1049658072410828816819309)
      ·
        refine ⟨393621777154060806307241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1049658072410828816819309 393621777154060806307241)
        ·
          refine ⟨295216332865545604730431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393621777154060806307241 295216332865545604730431)
          ·
            refine ⟨442824499298318407095647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295216332865545604730431 442824499298318407095647)
            ·
              refine ⟨664236748947477610643471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442824499298318407095647 664236748947477610643471)
              ·
                refine ⟨996355123421216415965207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 664236748947477610643471 996355123421216415965207)
                ·
                  refine ⟨1494532685131824623947811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 996355123421216415965207 1494532685131824623947811)
                  ·
                    refine ⟨2241799027697736935921717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1494532685131824623947811 2241799027697736935921717)
                    ·
                      refine ⟨210168658846662837742661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2241799027697736935921717 210168658846662837742661)
                      ·
                        rfl

theorem cell23_409302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_409302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409302 prefixEnd_409302 := by exact prefixLift 409302
  have htrace : WordTrace (prefixWord ++ tailWord_409302) baseStart_409302 baseEnd_409302 := by
    simpa [prefixWord, tailWord_409302, baseEnd_409302] using wordTrace_append hprefix tailTrace_409302
  have hstable : (prefixWord ++ tailWord_409302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409302).length < 2 ^ (prefixWord ++ tailWord_409302).sum := by decide
  have hdescent : baseEnd_409302 < baseStart_409302 := by decide
  rcases family_descends (prefixWord ++ tailWord_409302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409315 : List Nat := [1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 3]
def baseStart_409315 : Nat := 118140960795 + 409315 * 2 ^ 59
def prefixEnd_409315 : Nat := 4983230072969 + 3 ^ 40 * 409315 * 2
def baseEnd_409315 : Nat := 210175334095171286880101

theorem tailTrace_409315 : CollatzResearch.WordTrace tailWord_409315 prefixEnd_409315 210175334095171286880101 := by
  unfold tailWord_409315
  simp only [CollatzResearch.WordTrace]
  refine ⟨14928944512129135281653399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9952629674752756854435599 14928944512129135281653399)
  ·
    refine ⟨22393416768193702922480099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14928944512129135281653399 22393416768193702922480099)
    ·
      refine ⟨33590125152290554383720149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22393416768193702922480099 33590125152290554383720149)
      ·
        refine ⟨787268558256809868368441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33590125152290554383720149 787268558256809868368441)
        ·
          refine ⟨590451418692607401276331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787268558256809868368441 590451418692607401276331)
          ·
            refine ⟨885677128038911101914497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590451418692607401276331 885677128038911101914497)
            ·
              refine ⟨664257846029183326435873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885677128038911101914497 664257846029183326435873)
              ·
                refine ⟨498193384521887494826905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664257846029183326435873 498193384521887494826905)
                ·
                  refine ⟨373645038391415621120179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498193384521887494826905 373645038391415621120179)
                  ·
                    refine ⟨560467557587123431680269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 373645038391415621120179 560467557587123431680269)
                    ·
                      refine ⟨210175334095171286880101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560467557587123431680269 210175334095171286880101)
                      ·
                        rfl

theorem cell23_409315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_409315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409315 prefixEnd_409315 := by exact prefixLift 409315
  have htrace : WordTrace (prefixWord ++ tailWord_409315) baseStart_409315 baseEnd_409315 := by
    simpa [prefixWord, tailWord_409315, baseEnd_409315] using wordTrace_append hprefix tailTrace_409315
  have hstable : (prefixWord ++ tailWord_409315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409315).length < 2 ^ (prefixWord ++ tailWord_409315).sum := by decide
  have hdescent : baseEnd_409315 < baseStart_409315 := by decide
  rcases family_descends (prefixWord ++ tailWord_409315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409324 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_409324 : Nat := 118140960795 + 409324 * 2 ^ 59
def prefixEnd_409324 : Nat := 4983230072969 + 3 ^ 40 * 409324 * 2
def baseEnd_409324 : Nat := 210179955421061751667559

theorem tailTrace_409324 : CollatzResearch.WordTrace tailWord_409324 prefixEnd_409324 210179955421061751667559 := by
  unfold tailWord_409324
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464636384548264909365513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9952848512731019879154017 7464636384548264909365513)
  ·
    refine ⟨5598477288411198682024135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7464636384548264909365513 5598477288411198682024135)
    ·
      refine ⟨8397715932616798023036203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5598477288411198682024135 8397715932616798023036203)
      ·
        refine ⟨12596573898925197034554305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8397715932616798023036203 12596573898925197034554305)
        ·
          refine ⟨9447430424193897775915729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12596573898925197034554305 9447430424193897775915729)
          ·
            refine ⟨7085572818145423331936797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9447430424193897775915729 7085572818145423331936797)
            ·
              refine ⟨2657089806804533749476299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7085572818145423331936797 2657089806804533749476299)
              ·
                refine ⟨3985634710206800624214449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2657089806804533749476299 3985634710206800624214449)
                ·
                  refine ⟨2989226032655100468160837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3985634710206800624214449 2989226032655100468160837)
                  ·
                    refine ⟨560479881122831337780157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2989226032655100468160837 560479881122831337780157)
                    ·
                      refine ⟨210179955421061751667559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560479881122831337780157 210179955421061751667559)
                      ·
                        rfl

theorem cell23_409324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_409324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409324 prefixEnd_409324 := by exact prefixLift 409324
  have htrace : WordTrace (prefixWord ++ tailWord_409324) baseStart_409324 baseEnd_409324 := by
    simpa [prefixWord, tailWord_409324, baseEnd_409324] using wordTrace_append hprefix tailTrace_409324
  have hstable : (prefixWord ++ tailWord_409324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409324).length < 2 ^ (prefixWord ++ tailWord_409324).sum := by decide
  have hdescent : baseEnd_409324 < baseStart_409324 := by decide
  rcases family_descends (prefixWord ++ tailWord_409324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409332 : List Nat := [2, 6, 1, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_409332 : Nat := 118140960795 + 409332 * 2 ^ 59
def prefixEnd_409332 : Nat := 4983230072969 + 3 ^ 40 * 409332 * 2
def baseEnd_409332 : Nat := 210184063266297720367523

theorem tailTrace_409332 : CollatzResearch.WordTrace tailWord_409332 prefixEnd_409332 210184063266297720367523 := by
  unfold tailWord_409332
  simp only [CollatzResearch.WordTrace]
  refine ⟨7464782276533773592511125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9953043035378364790014833 7464782276533773592511125)
  ·
    refine ⟨349911669212520637148959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7464782276533773592511125 349911669212520637148959)
    ·
      refine ⟨524867503818780955723439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349911669212520637148959 524867503818780955723439)
      ·
        refine ⟨787301255728171433585159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524867503818780955723439 787301255728171433585159)
        ·
          refine ⟨1180951883592257150377739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787301255728171433585159 1180951883592257150377739)
          ·
            refine ⟨1771427825388385725566609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1180951883592257150377739 1771427825388385725566609)
            ·
              refine ⟨1328570869041289294174957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1771427825388385725566609 1328570869041289294174957)
              ·
                refine ⟨498214075890483485315609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1328570869041289294174957 498214075890483485315609)
                ·
                  refine ⟨373660556917862613986707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498214075890483485315609 373660556917862613986707)
                  ·
                    refine ⟨560490835376793920980061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 373660556917862613986707 560490835376793920980061)
                    ·
                      refine ⟨210184063266297720367523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560490835376793920980061 210184063266297720367523)
                      ·
                        rfl

theorem cell23_409332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_409332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409332 prefixEnd_409332 := by exact prefixLift 409332
  have htrace : WordTrace (prefixWord ++ tailWord_409332) baseStart_409332 baseEnd_409332 := by
    simpa [prefixWord, tailWord_409332, baseEnd_409332] using wordTrace_append hprefix tailTrace_409332
  have hstable : (prefixWord ++ tailWord_409332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409332).length < 2 ^ (prefixWord ++ tailWord_409332).sum := by decide
  have hdescent : baseEnd_409332 < baseStart_409332 := by decide
  rcases family_descends (prefixWord ++ tailWord_409332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409350 : List Nat := [6, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_409350 : Nat := 118140960795 + 409350 * 2 ^ 59
def prefixEnd_409350 : Nat := 4983230072969 + 3 ^ 40 * 409350 * 2
def baseEnd_409350 : Nat := 210193305918078649942441

theorem tailTrace_409350 : CollatzResearch.WordTrace tailWord_409350 prefixEnd_409350 210193305918078649942441 := by
  unfold tailWord_409350
  simp only [CollatzResearch.WordTrace]
  refine ⟨466569408343823008099297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9953480711334890839451669 466569408343823008099297)
  ·
    refine ⟨349927056257867256074473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 466569408343823008099297 349927056257867256074473)
    ·
      refine ⟨262445292193400442055855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 349927056257867256074473 262445292193400442055855)
      ·
        refine ⟨393667938290100663083783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262445292193400442055855 393667938290100663083783)
        ·
          refine ⟨590501907435150994625675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393667938290100663083783 590501907435150994625675)
          ·
            refine ⟨885752861152726491938513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590501907435150994625675 885752861152726491938513)
            ·
              refine ⟨664314645864544868953885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885752861152726491938513 664314645864544868953885)
              ·
                refine ⟨249117992199204325857707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664314645864544868953885 249117992199204325857707)
                ·
                  refine ⟨373676988298806488786561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249117992199204325857707 373676988298806488786561)
                  ·
                    refine ⟨280257741224104866589921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373676988298806488786561 280257741224104866589921)
                    ·
                      refine ⟨210193305918078649942441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280257741224104866589921 210193305918078649942441)
                      ·
                        rfl

theorem cell23_409350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_409350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409350 prefixEnd_409350 := by exact prefixLift 409350
  have htrace : WordTrace (prefixWord ++ tailWord_409350) baseStart_409350 baseEnd_409350 := by
    simpa [prefixWord, tailWord_409350, baseEnd_409350] using wordTrace_append hprefix tailTrace_409350
  have hstable : (prefixWord ++ tailWord_409350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409350).length < 2 ^ (prefixWord ++ tailWord_409350).sum := by decide
  have hdescent : baseEnd_409350 < baseStart_409350 := by decide
  rcases family_descends (prefixWord ++ tailWord_409350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409428 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 2, 1, 4]
def baseStart_409428 : Nat := 118140960795 + 409428 * 2 ^ 59
def prefixEnd_409428 : Nat := 4983230072969 + 3 ^ 40 * 409428 * 2
def baseEnd_409428 : Nat := 210233357409129344767081

theorem tailTrace_409428 : CollatzResearch.WordTrace tailWord_409428 prefixEnd_409428 210233357409129344767081 := by
  unfold tailWord_409428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7466532980359877790258469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9955377307146503720344625 7466532980359877790258469)
  ·
    refine ⟨1399974933817477085673463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7466532980359877790258469 1399974933817477085673463)
    ·
      refine ⟨2099962400726215628510195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1399974933817477085673463 2099962400726215628510195)
      ·
        refine ⟨3149943601089323442765293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099962400726215628510195 3149943601089323442765293)
        ·
          refine ⟨1181228850408496291036985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3149943601089323442765293 1181228850408496291036985)
          ·
            refine ⟨885921637806372218277739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181228850408496291036985 885921637806372218277739)
            ·
              refine ⟨1328882456709558327416609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885921637806372218277739 1328882456709558327416609)
              ·
                refine ⟨996661842532168745562457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1328882456709558327416609 996661842532168745562457)
                ·
                  refine ⟨747496381899126559171843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 996661842532168745562457 747496381899126559171843)
                  ·
                    refine ⟨1121244572848689838757765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747496381899126559171843 1121244572848689838757765)
                    ·
                      refine ⟨210233357409129344767081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1121244572848689838757765 210233357409129344767081)
                      ·
                        rfl

theorem cell23_409428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_409428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409428 prefixEnd_409428 := by exact prefixLift 409428
  have htrace : WordTrace (prefixWord ++ tailWord_409428) baseStart_409428 baseEnd_409428 := by
    simpa [prefixWord, tailWord_409428, baseEnd_409428] using wordTrace_append hprefix tailTrace_409428
  have hstable : (prefixWord ++ tailWord_409428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409428).length < 2 ^ (prefixWord ++ tailWord_409428).sum := by decide
  have hdescent : baseEnd_409428 < baseStart_409428 := by decide
  rcases family_descends (prefixWord ++ tailWord_409428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409434 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 8]
def baseStart_409434 : Nat := 118140960795 + 409434 * 2 ^ 59
def prefixEnd_409434 : Nat := 4983230072969 + 3 ^ 40 * 409434 * 2
def baseEnd_409434 : Nat := 23359604254784035699117

theorem tailTrace_409434 : CollatzResearch.WordTrace tailWord_409434 prefixEnd_409434 23359604254784035699117 := by
  unfold tailWord_409434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733321199674504651308839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9955523199132012403490237 3733321199674504651308839)
  ·
    refine ⟨5599981799511756976963259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733321199674504651308839 5599981799511756976963259)
    ·
      refine ⟨8399972699267635465444889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5599981799511756976963259 8399972699267635465444889)
      ·
        refine ⟨6299979524450726599083667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8399972699267635465444889 6299979524450726599083667)
        ·
          refine ⟨9449969286676089898625501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6299979524450726599083667 9449969286676089898625501)
          ·
            refine ⟨3543738482503533711984563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9449969286676089898625501 3543738482503533711984563)
            ·
              refine ⟨5315607723755300567976845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3543738482503533711984563 5315607723755300567976845)
              ·
                refine ⟨1993352896408237712991317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5315607723755300567976845 1993352896408237712991317)
                ·
                  refine ⟨23359604254784035699117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1993352896408237712991317 23359604254784035699117)
                  ·
                    rfl

theorem cell23_409434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 8].length) (baseStart_409434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409434 prefixEnd_409434 := by exact prefixLift 409434
  have htrace : WordTrace (prefixWord ++ tailWord_409434) baseStart_409434 baseEnd_409434 := by
    simpa [prefixWord, tailWord_409434, baseEnd_409434] using wordTrace_append hprefix tailTrace_409434
  have hstable : (prefixWord ++ tailWord_409434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409434).length < 2 ^ (prefixWord ++ tailWord_409434).sum := by decide
  have hdescent : baseEnd_409434 < baseStart_409434 := by decide
  rcases family_descends (prefixWord ++ tailWord_409434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409552 : List Nat := [2, 1, 1, 1, 1, 2, 6, 4, 1, 2, 2]
def baseStart_409552 : Nat := 118140960795 + 409552 * 2 ^ 59
def prefixEnd_409552 : Nat := 4983230072969 + 3 ^ 40 * 409552 * 2
def baseEnd_409552 : Nat := 210297029010286859616511

theorem tailTrace_409552 : CollatzResearch.WordTrace tailWord_409552 prefixEnd_409552 210297029010286859616511 := by
  unfold tailWord_409552
  simp only [CollatzResearch.WordTrace]
  refine ⟨7468794306135262379015455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9958392408180349838687273 7468794306135262379015455)
  ·
    refine ⟨11203191459202893568523183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7468794306135262379015455 11203191459202893568523183)
    ·
      refine ⟨16804787188804340352784775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11203191459202893568523183 16804787188804340352784775)
      ·
        refine ⟨25207180783206510529177163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16804787188804340352784775 25207180783206510529177163)
        ·
          refine ⟨37810771174809765793765745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25207180783206510529177163 37810771174809765793765745)
          ·
            refine ⟨28358078381107324345324309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37810771174809765793765745 28358078381107324345324309)
            ·
              refine ⟨1329284924114405828687077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28358078381107324345324309 1329284924114405828687077)
              ·
                refine ⟨249240923271451092878827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1329284924114405828687077 249240923271451092878827)
                ·
                  refine ⟨373861384907176639318241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249240923271451092878827 373861384907176639318241)
                  ·
                    refine ⟨280396038680382479488681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 373861384907176639318241 280396038680382479488681)
                    ·
                      refine ⟨210297029010286859616511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280396038680382479488681 210297029010286859616511)
                      ·
                        rfl

theorem cell23_409552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 4, 1, 2, 2].length) (baseStart_409552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409552 prefixEnd_409552 := by exact prefixLift 409552
  have htrace : WordTrace (prefixWord ++ tailWord_409552) baseStart_409552 baseEnd_409552 := by
    simpa [prefixWord, tailWord_409552, baseEnd_409552] using wordTrace_append hprefix tailTrace_409552
  have hstable : (prefixWord ++ tailWord_409552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409552).length < 2 ^ (prefixWord ++ tailWord_409552).sum := by decide
  have hdescent : baseEnd_409552 < baseStart_409552 := by decide
  rcases family_descends (prefixWord ++ tailWord_409552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409562 : List Nat := [3, 1, 1, 2, 5, 1, 3, 1, 2, 4]
def baseStart_409562 : Nat := 118140960795 + 409562 * 2 ^ 59
def prefixEnd_409562 : Nat := 4983230072969 + 3 ^ 40 * 409562 * 2
def baseEnd_409562 : Nat := 70100721272277273497155

theorem tailTrace_409562 : CollatzResearch.WordTrace tailWord_409562 prefixEnd_409562 70100721272277273497155 := by
  unfold tailWord_409562
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734488335558574116473735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9958635561489530977263293 3734488335558574116473735)
  ·
    refine ⟨5601732503337861174710603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3734488335558574116473735 5601732503337861174710603)
    ·
      refine ⟨8402598755006791762065905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5601732503337861174710603 8402598755006791762065905)
      ·
        refine ⟨6301949066255093821549429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8402598755006791762065905 6301949066255093821549429)
        ·
          refine ⟨590807724961415045770259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6301949066255093821549429 590807724961415045770259)
          ·
            refine ⟨886211587442122568655389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590807724961415045770259 886211587442122568655389)
            ·
              refine ⟨332329345290795963245771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 886211587442122568655389 332329345290795963245771)
              ·
                refine ⟨498494017936193944868657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332329345290795963245771 498494017936193944868657)
                ·
                  refine ⟨373870513452145458651493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498494017936193944868657 373870513452145458651493)
                  ·
                    refine ⟨70100721272277273497155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373870513452145458651493 70100721272277273497155)
                    ·
                      rfl

theorem cell23_409562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_409562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409562 prefixEnd_409562 := by exact prefixLift 409562
  have htrace : WordTrace (prefixWord ++ tailWord_409562) baseStart_409562 baseEnd_409562 := by
    simpa [prefixWord, tailWord_409562, baseEnd_409562] using wordTrace_append hprefix tailTrace_409562
  have hstable : (prefixWord ++ tailWord_409562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409562).length < 2 ^ (prefixWord ++ tailWord_409562).sum := by decide
  have hdescent : baseEnd_409562 < baseStart_409562 := by decide
  rcases family_descends (prefixWord ++ tailWord_409562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409575 : List Nat := [1, 1, 5, 2, 3, 2, 2, 7]
def baseStart_409575 : Nat := 118140960795 + 409575 * 2 ^ 59
def prefixEnd_409575 : Nat := 4983230072969 + 3 ^ 40 * 409575 * 2
def baseEnd_409575 : Nat := 7789216261679269245515

theorem tailTrace_409575 : CollatzResearch.WordTrace tailWord_409575 prefixEnd_409575 7789216261679269245515 := by
  unfold tailWord_409575
  simp only [CollatzResearch.WordTrace]
  refine ⟨14938427491187199686118179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9958951660791466457412119 14938427491187199686118179)
  ·
    refine ⟨22407641236780799529177269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14938427491187199686118179 22407641236780799529177269)
    ·
      refine ⟨2100716365948199955860369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22407641236780799529177269 2100716365948199955860369)
      ·
        refine ⟨1575537274461149966895277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2100716365948199955860369 1575537274461149966895277)
        ·
          refine ⟨590826477922931237585729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1575537274461149966895277 590826477922931237585729)
          ·
            refine ⟨443119858442198428189297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590826477922931237585729 443119858442198428189297)
            ·
              refine ⟨332339893831648821141973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443119858442198428189297 332339893831648821141973)
              ·
                refine ⟨7789216261679269245515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 332339893831648821141973 7789216261679269245515)
                ·
                  rfl

theorem cell23_409575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 7].length) (baseStart_409575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409575 prefixEnd_409575 := by exact prefixLift 409575
  have htrace : WordTrace (prefixWord ++ tailWord_409575) baseStart_409575 baseEnd_409575 := by
    simpa [prefixWord, tailWord_409575, baseEnd_409575] using wordTrace_append hprefix tailTrace_409575
  have hstable : (prefixWord ++ tailWord_409575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409575).length < 2 ^ (prefixWord ++ tailWord_409575).sum := by decide
  have hdescent : baseEnd_409575 < baseStart_409575 := by decide
  rcases family_descends (prefixWord ++ tailWord_409575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409595 : List Nat := [1, 1, 1, 1, 1, 3, 6, 3, 1, 3, 2]
def baseStart_409595 : Nat := 118140960795 + 409595 * 2 ^ 59
def prefixEnd_409595 : Nat := 4983230072969 + 3 ^ 40 * 409595 * 2
def baseEnd_409595 : Nat := 210319108678430191378813

theorem tailTrace_409595 : CollatzResearch.WordTrace tailWord_409595 prefixEnd_409595 210319108678430191378813 := by
  unfold tailWord_409595
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939156951114743101846239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9959437967409828734564159 14939156951114743101846239)
  ·
    refine ⟨22408735426672114652769359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14939156951114743101846239 22408735426672114652769359)
    ·
      refine ⟨33613103140008171979154039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22408735426672114652769359 33613103140008171979154039)
      ·
        refine ⟨50419654710012257968731059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33613103140008171979154039 50419654710012257968731059)
        ·
          refine ⟨75629482065018386953096589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50419654710012257968731059 75629482065018386953096589)
          ·
            refine ⟨28361055774381895107411221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75629482065018386953096589 28361055774381895107411221)
            ·
              refine ⟨1329424489424151333159901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28361055774381895107411221 1329424489424151333159901)
              ·
                refine ⟨498534183534056749934963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1329424489424151333159901 498534183534056749934963)
                ·
                  refine ⟨747801275301085124902445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498534183534056749934963 747801275301085124902445)
                  ·
                    refine ⟨280425478237906921838417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747801275301085124902445 280425478237906921838417)
                    ·
                      refine ⟨210319108678430191378813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280425478237906921838417 210319108678430191378813)
                      ·
                        rfl

theorem cell23_409595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 3, 2].length) (baseStart_409595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409595 prefixEnd_409595 := by exact prefixLift 409595
  have htrace : WordTrace (prefixWord ++ tailWord_409595) baseStart_409595 baseEnd_409595 := by
    simpa [prefixWord, tailWord_409595, baseEnd_409595] using wordTrace_append hprefix tailTrace_409595
  have hstable : (prefixWord ++ tailWord_409595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409595).length < 2 ^ (prefixWord ++ tailWord_409595).sum := by decide
  have hdescent : baseEnd_409595 < baseStart_409595 := by decide
  rcases family_descends (prefixWord ++ tailWord_409595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409611 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5]
def baseStart_409611 : Nat := 118140960795 + 409611 * 2 ^ 59
def prefixEnd_409611 : Nat := 4983230072969 + 3 ^ 40 * 409611 * 2
def baseEnd_409611 : Nat := 210327324368902128778739

theorem tailTrace_409611 : CollatzResearch.WordTrace tailWord_409611 prefixEnd_409611 210327324368902128778739 := by
  unfold tailWord_409611
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939740519056777834428687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9959827012704518556285791 14939740519056777834428687)
  ·
    refine ⟨22409610778585166751643031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14939740519056777834428687 22409610778585166751643031)
    ·
      refine ⟨33614416167877750127464547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22409610778585166751643031 33614416167877750127464547)
      ·
        refine ⟨50421624251816625191196821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33614416167877750127464547 50421624251816625191196821)
        ·
          refine ⟨2363513636803904305837351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50421624251816625191196821 2363513636803904305837351)
          ·
            refine ⟨3545270455205856458756027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2363513636803904305837351 3545270455205856458756027)
            ·
              refine ⟨5317905682808784688134041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3545270455205856458756027 5317905682808784688134041)
              ·
                refine ⟨3988429262106588516100531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5317905682808784688134041 3988429262106588516100531)
                ·
                  refine ⟨5982643893159882774150797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3988429262106588516100531 5982643893159882774150797)
                  ·
                    refine ⟨2243491459934956040306549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5982643893159882774150797 2243491459934956040306549)
                    ·
                      refine ⟨210327324368902128778739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2243491459934956040306549 210327324368902128778739)
                      ·
                        rfl

theorem cell23_409611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_409611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409611 prefixEnd_409611 := by exact prefixLift 409611
  have htrace : WordTrace (prefixWord ++ tailWord_409611) baseStart_409611 baseEnd_409611 := by
    simpa [prefixWord, tailWord_409611, baseEnd_409611] using wordTrace_append hprefix tailTrace_409611
  have hstable : (prefixWord ++ tailWord_409611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409611).length < 2 ^ (prefixWord ++ tailWord_409611).sum := by decide
  have hdescent : baseEnd_409611 < baseStart_409611 := by decide
  rcases family_descends (prefixWord ++ tailWord_409611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409613 : List Nat := [1, 7, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_409613 : Nat := 118140960795 + 409613 * 2 ^ 59
def prefixEnd_409613 : Nat := 4983230072969 + 3 ^ 40 * 409613 * 2
def baseEnd_409613 : Nat := 70109450443403706984577

theorem tailTrace_409613 : CollatzResearch.WordTrace tailWord_409613 prefixEnd_409613 70109450443403706984577 := by
  unfold tailWord_409613
  simp only [CollatzResearch.WordTrace]
  refine ⟨14939813465049532176001493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9959875643366354784000995 14939813465049532176001493)
  ·
    refine ⟨350151878087098410375035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14939813465049532176001493 350151878087098410375035)
    ·
      refine ⟨525227817130647615562553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350151878087098410375035 525227817130647615562553)
      ·
        refine ⟨393920862847985711671915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 525227817130647615562553 393920862847985711671915)
        ·
          refine ⟨590881294271978567507873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393920862847985711671915 590881294271978567507873)
          ·
            refine ⟨443160970703983925630905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 590881294271978567507873 443160970703983925630905)
            ·
              refine ⟨332370728027987944223179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443160970703983925630905 332370728027987944223179)
              ·
                refine ⟨498556092041981916334769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332370728027987944223179 498556092041981916334769)
                ·
                  refine ⟨373917069031486437251077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498556092041981916334769 373917069031486437251077)
                  ·
                    refine ⟨70109450443403706984577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 373917069031486437251077 70109450443403706984577)
                    ·
                      rfl

theorem cell23_409613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_409613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409613 prefixEnd_409613 := by exact prefixLift 409613
  have htrace : WordTrace (prefixWord ++ tailWord_409613) baseStart_409613 baseEnd_409613 := by
    simpa [prefixWord, tailWord_409613, baseEnd_409613] using wordTrace_append hprefix tailTrace_409613
  have hstable : (prefixWord ++ tailWord_409613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409613).length < 2 ^ (prefixWord ++ tailWord_409613).sum := by decide
  have hdescent : baseEnd_409613 < baseStart_409613 := by decide
  rcases family_descends (prefixWord ++ tailWord_409613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409628 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_409628 : Nat := 118140960795 + 409628 * 2 ^ 59
def prefixEnd_409628 : Nat := 4983230072969 + 3 ^ 40 * 409628 * 2
def baseEnd_409628 : Nat := 210336053540028562266161

theorem tailTrace_409628 : CollatzResearch.WordTrace tailWord_409628 prefixEnd_409628 210336053540028562266161 := by
  unfold tailWord_409628
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470180279997594868898769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9960240373330126491865025 7470180279997594868898769)
  ·
    refine ⟨5602635209998196151674077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7470180279997594868898769 5602635209998196151674077)
    ·
      refine ⟨2100988203749323556877779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5602635209998196151674077 2100988203749323556877779)
      ·
        refine ⟨3151482305623985335316669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2100988203749323556877779 3151482305623985335316669)
        ·
          refine ⟨1181805864608994500743751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3151482305623985335316669 1181805864608994500743751)
          ·
            refine ⟨1772708796913491751115627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181805864608994500743751 1772708796913491751115627)
            ·
              refine ⟨2659063195370237626673441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1772708796913491751115627 2659063195370237626673441)
              ·
                refine ⟨1994297396527678220005081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2659063195370237626673441 1994297396527678220005081)
                ·
                  refine ⟨1495723047395758665003811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994297396527678220005081 1495723047395758665003811)
                  ·
                    refine ⟨2243584571093637997505717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1495723047395758665003811 2243584571093637997505717)
                    ·
                      refine ⟨210336053540028562266161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2243584571093637997505717 210336053540028562266161)
                      ·
                        rfl

theorem cell23_409628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_409628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409628 prefixEnd_409628 := by exact prefixLift 409628
  have htrace : WordTrace (prefixWord ++ tailWord_409628) baseStart_409628 baseEnd_409628 := by
    simpa [prefixWord, tailWord_409628, baseEnd_409628] using wordTrace_append hprefix tailTrace_409628
  have hstable : (prefixWord ++ tailWord_409628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409628).length < 2 ^ (prefixWord ++ tailWord_409628).sum := by decide
  have hdescent : baseEnd_409628 < baseStart_409628 := by decide
  rcases family_descends (prefixWord ++ tailWord_409628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409629 : List Nat := [1, 4, 2, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_409629 : Nat := 118140960795 + 409629 * 2 ^ 59
def prefixEnd_409629 : Nat := 4983230072969 + 3 ^ 40 * 409629 * 2
def baseEnd_409629 : Nat := 210336567020683058353657

theorem tailTrace_409629 : CollatzResearch.WordTrace tailWord_409629 prefixEnd_409629 210336567020683058353657 := by
  unfold tailWord_409629
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940397032991566908583941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9960264688661044605722627 14940397032991566908583941)
  ·
    refine ⟨2801324443685918795359489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14940397032991566908583941 2801324443685918795359489)
    ·
      refine ⟨2100993332764439096519617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2801324443685918795359489 2100993332764439096519617)
      ·
        refine ⟨1575744999573329322389713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2100993332764439096519617 1575744999573329322389713)
        ·
          refine ⟨1181808749679996991792285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575744999573329322389713 1181808749679996991792285)
          ·
            refine ⟨443178281129998871922107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1181808749679996991792285 443178281129998871922107)
            ·
              refine ⟨664767421694998307883161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443178281129998871922107 664767421694998307883161)
              ·
                refine ⟨498575566271248730912371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 664767421694998307883161 498575566271248730912371)
                ·
                  refine ⟨747863349406873096368557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498575566271248730912371 747863349406873096368557)
                  ·
                    refine ⟨280448756027577411138209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 747863349406873096368557 280448756027577411138209)
                    ·
                      refine ⟨210336567020683058353657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280448756027577411138209 210336567020683058353657)
                      ·
                        rfl

theorem cell23_409629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_409629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409629 prefixEnd_409629 := by exact prefixLift 409629
  have htrace : WordTrace (prefixWord ++ tailWord_409629) baseStart_409629 baseEnd_409629 := by
    simpa [prefixWord, tailWord_409629, baseEnd_409629] using wordTrace_append hprefix tailTrace_409629
  have hstable : (prefixWord ++ tailWord_409629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409629).length < 2 ^ (prefixWord ++ tailWord_409629).sum := by decide
  have hdescent : baseEnd_409629 < baseStart_409629 := by decide
  rcases family_descends (prefixWord ++ tailWord_409629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409631 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 9]
def baseStart_409631 : Nat := 118140960795 + 409631 * 2 ^ 59
def prefixEnd_409631 : Nat := 4983230072969 + 3 ^ 40 * 409631 * 2
def baseEnd_409631 : Nat := 23370843775776894503183

theorem tailTrace_409631 : CollatzResearch.WordTrace tailWord_409631 prefixEnd_409631 23370843775776894503183 := by
  unfold tailWord_409631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940469978984321250156747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9960313319322880833437831 14940469978984321250156747)
  ·
    refine ⟨22410704968476481875235121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14940469978984321250156747 22410704968476481875235121)
    ·
      refine ⟨16808028726357361406426341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22410704968476481875235121 16808028726357361406426341)
      ·
        refine ⟨3151505386192005263704939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16808028726357361406426341 3151505386192005263704939)
        ·
          refine ⟨4727258079288007895557409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3151505386192005263704939 4727258079288007895557409)
          ·
            refine ⟨3545443559466005921668057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4727258079288007895557409 3545443559466005921668057)
            ·
              refine ⟨2659082669599504441251043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3545443559466005921668057 2659082669599504441251043)
              ·
                refine ⟨3988624004399256661876565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2659082669599504441251043 3988624004399256661876565)
                ·
                  refine ⟨23370843775776894503183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3988624004399256661876565 23370843775776894503183)
                  ·
                    rfl

theorem cell23_409631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 9].length) (baseStart_409631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409631 prefixEnd_409631 := by exact prefixLift 409631
  have htrace : WordTrace (prefixWord ++ tailWord_409631) baseStart_409631 baseEnd_409631 := by
    simpa [prefixWord, tailWord_409631, baseEnd_409631] using wordTrace_append hprefix tailTrace_409631
  have hstable : (prefixWord ++ tailWord_409631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409631).length < 2 ^ (prefixWord ++ tailWord_409631).sum := by decide
  have hdescent : baseEnd_409631 < baseStart_409631 := by decide
  rcases family_descends (prefixWord ++ tailWord_409631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409642 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_409642 : Nat := 118140960795 + 409642 * 2 ^ 59
def prefixEnd_409642 : Nat := 4983230072969 + 3 ^ 40 * 409642 * 2
def baseEnd_409642 : Nat := 210343242269191507491097

theorem tailTrace_409642 : CollatzResearch.WordTrace tailWord_409642 prefixEnd_409642 210343242269191507491097 := by
  unfold tailWord_409642
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735217795486117532201795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9960580787962980085871453 3735217795486117532201795)
  ·
    refine ⟨5602826693229176298302693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3735217795486117532201795 5602826693229176298302693)
    ·
      refine ⟨1050530004980470555931755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5602826693229176298302693 1050530004980470555931755)
      ·
        refine ⟨1575795007470705833897633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050530004980470555931755 1575795007470705833897633)
        ·
          refine ⟨1181846255603029375423225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1575795007470705833897633 1181846255603029375423225)
          ·
            refine ⟨886384691702272031567419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1181846255603029375423225 886384691702272031567419)
            ·
              refine ⟨1329577037553408047351129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 886384691702272031567419 1329577037553408047351129)
              ·
                refine ⟨997182778165056035513347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1329577037553408047351129 997182778165056035513347)
                ·
                  refine ⟨1495774167247584053270021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 997182778165056035513347 1495774167247584053270021)
                  ·
                    refine ⟨280457656358922009988129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1495774167247584053270021 280457656358922009988129)
                    ·
                      refine ⟨210343242269191507491097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 280457656358922009988129 210343242269191507491097)
                      ·
                        rfl

theorem cell23_409642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_409642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409642 prefixEnd_409642 := by exact prefixLift 409642
  have htrace : WordTrace (prefixWord ++ tailWord_409642) baseStart_409642 baseEnd_409642 := by
    simpa [prefixWord, tailWord_409642, baseEnd_409642] using wordTrace_append hprefix tailTrace_409642
  have hstable : (prefixWord ++ tailWord_409642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409642).length < 2 ^ (prefixWord ++ tailWord_409642).sum := by decide
  have hdescent : baseEnd_409642 < baseStart_409642 := by decide
  rcases family_descends (prefixWord ++ tailWord_409642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409658 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_409658 : Nat := 118140960795 + 409658 * 2 ^ 59
def prefixEnd_409658 : Nat := 4983230072969 + 3 ^ 40 * 409658 * 2
def baseEnd_409658 : Nat := 210351457959663444891023

theorem tailTrace_409658 : CollatzResearch.WordTrace tailWord_409658 prefixEnd_409658 210351457959663444891023 := by
  unfold tailWord_409658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3735363687471626215347407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9960969833257669907593085 3735363687471626215347407)
  ·
    refine ⟨5603045531207439323021111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3735363687471626215347407 5603045531207439323021111)
    ·
      refine ⟨8404568296811158984531667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5603045531207439323021111 8404568296811158984531667)
      ·
        refine ⟨12606852445216738476797501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404568296811158984531667 12606852445216738476797501)
        ·
          refine ⟨4727569666956276928799063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12606852445216738476797501 4727569666956276928799063)
          ·
            refine ⟨7091354500434415393198595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4727569666956276928799063 7091354500434415393198595)
            ·
              refine ⟨10637031750651623089797893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7091354500434415393198595 10637031750651623089797893)
              ·
                refine ⟨1994443453247179329337105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10637031750651623089797893 1994443453247179329337105)
                ·
                  refine ⟨1495832589935384497002829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1994443453247179329337105 1495832589935384497002829)
                  ·
                    refine ⟨560937221225769186376061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1495832589935384497002829 560937221225769186376061)
                    ·
                      refine ⟨210351457959663444891023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 560937221225769186376061 210351457959663444891023)
                      ·
                        rfl

theorem cell23_409658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_409658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409658 prefixEnd_409658 := by exact prefixLift 409658
  have htrace : WordTrace (prefixWord ++ tailWord_409658) baseStart_409658 baseEnd_409658 := by
    simpa [prefixWord, tailWord_409658, baseEnd_409658] using wordTrace_append hprefix tailTrace_409658
  have hstable : (prefixWord ++ tailWord_409658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409658).length < 2 ^ (prefixWord ++ tailWord_409658).sum := by decide
  have hdescent : baseEnd_409658 < baseStart_409658 := by decide
  rcases family_descends (prefixWord ++ tailWord_409658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409725 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 3, 4]
def baseStart_409725 : Nat := 118140960795 + 409725 * 2 ^ 59
def prefixEnd_409725 : Nat := 4983230072969 + 3 ^ 40 * 409725 * 2
def baseEnd_409725 : Nat := 70128620387838227584405

theorem tailTrace_409725 : CollatzResearch.WordTrace tailWord_409725 prefixEnd_409725 70128620387838227584405 := by
  unfold tailWord_409725
  simp only [CollatzResearch.WordTrace]
  refine ⟨14943898440643775304078629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9962598960429183536052419 14943898440643775304078629)
  ·
    refine ⟨2801980957620707869514743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14943898440643775304078629 2801980957620707869514743)
    ·
      refine ⟨4202971436431061804272115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801980957620707869514743 4202971436431061804272115)
      ·
        refine ⟨6304457154646592706408173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202971436431061804272115 6304457154646592706408173)
        ·
          refine ⟨2364171432992472264903065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6304457154646592706408173 2364171432992472264903065)
          ·
            refine ⟨1773128574744354198677299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2364171432992472264903065 1773128574744354198677299)
            ·
              refine ⟨2659692862116531298015949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773128574744354198677299 2659692862116531298015949)
              ·
                refine ⟨997384823293699236755981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2659692862116531298015949 997384823293699236755981)
                ·
                  refine ⟨374019308735137213783493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 997384823293699236755981 374019308735137213783493)
                  ·
                    refine ⟨70128620387838227584405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374019308735137213783493 70128620387838227584405)
                    ·
                      rfl

theorem cell23_409725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_409725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409725 prefixEnd_409725 := by exact prefixLift 409725
  have htrace : WordTrace (prefixWord ++ tailWord_409725) baseStart_409725 baseEnd_409725 := by
    simpa [prefixWord, tailWord_409725, baseEnd_409725] using wordTrace_append hprefix tailTrace_409725
  have hstable : (prefixWord ++ tailWord_409725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409725).length < 2 ^ (prefixWord ++ tailWord_409725).sum := by decide
  have hdescent : baseEnd_409725 < baseStart_409725 := by decide
  rcases family_descends (prefixWord ++ tailWord_409725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409750 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_409750 : Nat := 118140960795 + 409750 * 2 ^ 59
def prefixEnd_409750 : Nat := 4983230072969 + 3 ^ 40 * 409750 * 2
def baseEnd_409750 : Nat := 23377633131097453882289

theorem tailTrace_409750 : CollatzResearch.WordTrace tailWord_409750 prefixEnd_409750 23377633131097453882289 := by
  unfold tailWord_409750
  simp only [CollatzResearch.WordTrace]
  refine ⟨934050641597075285858669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9963206843702136382492469 934050641597075285858669)
  ·
    refine ⟨350268990598903232197001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 934050641597075285858669 350268990598903232197001)
    ·
      refine ⟨262701742949177424147751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 350268990598903232197001 262701742949177424147751)
      ·
        refine ⟨394052614423766136221627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262701742949177424147751 394052614423766136221627)
        ·
          refine ⟨591078921635649204332441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394052614423766136221627 591078921635649204332441)
          ·
            refine ⟨443309191226736903249331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 591078921635649204332441 443309191226736903249331)
            ·
              refine ⟨664963786840105354873997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443309191226736903249331 664963786840105354873997)
              ·
                refine ⟨249361420065039508077749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664963786840105354873997 249361420065039508077749)
                ·
                  refine ⟨23377633131097453882289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249361420065039508077749 23377633131097453882289)
                  ·
                    rfl

theorem cell23_409750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_409750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409750 prefixEnd_409750 := by exact prefixLift 409750
  have htrace : WordTrace (prefixWord ++ tailWord_409750) baseStart_409750 baseEnd_409750 := by
    simpa [prefixWord, tailWord_409750, baseEnd_409750] using wordTrace_append hprefix tailTrace_409750
  have hstable : (prefixWord ++ tailWord_409750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409750).length < 2 ^ (prefixWord ++ tailWord_409750).sum := by decide
  have hdescent : baseEnd_409750 < baseStart_409750 := by decide
  rcases family_descends (prefixWord ++ tailWord_409750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409759 : List Nat := [1, 1, 2, 6, 1, 1, 3, 3, 1, 4]
def baseStart_409759 : Nat := 118140960795 + 409759 * 2 ^ 59
def prefixEnd_409759 : Nat := 4983230072969 + 3 ^ 40 * 409759 * 2
def baseEnd_409759 : Nat := 70134439835255849909353

theorem tailTrace_409759 : CollatzResearch.WordTrace tailWord_409759 prefixEnd_409759 70134439835255849909353 := by
  unfold tailWord_409759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14945138522520599110816331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9963425681680399407210887 14945138522520599110816331)
  ·
    refine ⟨22417707783780898666224497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14945138522520599110816331 22417707783780898666224497)
    ·
      refine ⟨16813280837835673999668373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22417707783780898666224497 16813280837835673999668373)
      ·
        refine ⟨788122539273547218734455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16813280837835673999668373 788122539273547218734455)
        ·
          refine ⟨1182183808910320828101683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788122539273547218734455 1182183808910320828101683)
          ·
            refine ⟨1773275713365481242152525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182183808910320828101683 1773275713365481242152525)
            ·
              refine ⟨664978392512055465807197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1773275713365481242152525 664978392512055465807197)
              ·
                refine ⟨249366897192020799677699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 664978392512055465807197 249366897192020799677699)
                ·
                  refine ⟨374050345788031199516549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249366897192020799677699 374050345788031199516549)
                  ·
                    refine ⟨70134439835255849909353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374050345788031199516549 70134439835255849909353)
                    ·
                      rfl

theorem cell23_409759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 3, 1, 4].length) (baseStart_409759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409759 prefixEnd_409759 := by exact prefixLift 409759
  have htrace : WordTrace (prefixWord ++ tailWord_409759) baseStart_409759 baseEnd_409759 := by
    simpa [prefixWord, tailWord_409759, baseEnd_409759] using wordTrace_append hprefix tailTrace_409759
  have hstable : (prefixWord ++ tailWord_409759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409759).length < 2 ^ (prefixWord ++ tailWord_409759).sum := by decide
  have hdescent : baseEnd_409759 < baseStart_409759 := by decide
  rcases family_descends (prefixWord ++ tailWord_409759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409832 : List Nat := [2, 1, 4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_409832 : Nat := 118140960795 + 409832 * 2 ^ 59
def prefixEnd_409832 : Nat := 4983230072969 + 3 ^ 40 * 409832 * 2
def baseEnd_409832 : Nat := 70146934531181921371741

theorem tailTrace_409832 : CollatzResearch.WordTrace tailWord_409832 prefixEnd_409832 70146934531181921371741 := by
  unfold tailWord_409832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7473900525628066289111875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9965200700837421718815833 7473900525628066289111875)
  ·
    refine ⟨11210850788442099433667813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7473900525628066289111875 11210850788442099433667813)
    ·
      refine ⟨2102034522832893643812715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11210850788442099433667813 2102034522832893643812715)
      ·
        refine ⟨3153051784249340465719073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102034522832893643812715 3153051784249340465719073)
        ·
          refine ⟨2364788838187005349289305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3153051784249340465719073 2364788838187005349289305)
          ·
            refine ⟨1773591628640254011966979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2364788838187005349289305 1773591628640254011966979)
            ·
              refine ⟨2660387442960381017950469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1773591628640254011966979 2660387442960381017950469)
              ·
                refine ⟨498822645555071440865713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2660387442960381017950469 498822645555071440865713)
                ·
                  refine ⟨374116984166303580649285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 498822645555071440865713 374116984166303580649285)
                  ·
                    refine ⟨70146934531181921371741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 374116984166303580649285 70146934531181921371741)
                    ·
                      rfl

theorem cell23_409832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_409832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_409832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_409832 prefixEnd_409832 := by exact prefixLift 409832
  have htrace : WordTrace (prefixWord ++ tailWord_409832) baseStart_409832 baseEnd_409832 := by
    simpa [prefixWord, tailWord_409832, baseEnd_409832] using wordTrace_append hprefix tailTrace_409832
  have hstable : (prefixWord ++ tailWord_409832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409832).length < 2 ^ (prefixWord ++ tailWord_409832).sum := by decide
  have hdescent : baseEnd_409832 < baseStart_409832 := by decide
  rcases family_descends (prefixWord ++ tailWord_409832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
