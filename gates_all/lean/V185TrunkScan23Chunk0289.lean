import V185TrunkScan23Chunk0288

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1708394 : List Nat := [3, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1708394 : Nat := 118140960795 + 1708394 * 2 ^ 59
def prefixEnd_1708394 : Nat := 4983230072969 + 3 ^ 40 * 1708394 * 2
def baseEnd_1708394 : Nat := 877227269257294134318245

theorem tailTrace_1708394 : CollatzResearch.WordTrace tailWord_1708394 prefixEnd_1708394 877227269257294134318245 := by
  unfold tailWord_1708394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15577562043196945827819059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41540165448525188874184157 15577562043196945827819059)
  ·
    refine ⟨23366343064795418741728589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15577562043196945827819059 23366343064795418741728589)
    ·
      refine ⟨8762378649298282028148221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23366343064795418741728589 8762378649298282028148221)
      ·
        refine ⟨3285891993486855760555583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8762378649298282028148221 3285891993486855760555583)
        ·
          refine ⟨4928837990230283640833375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285891993486855760555583 4928837990230283640833375)
          ·
            refine ⟨7393256985345425461250063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928837990230283640833375 7393256985345425461250063)
            ·
              refine ⟨11089885478018138191875095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393256985345425461250063 11089885478018138191875095)
              ·
                refine ⟨16634828217027207287812643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11089885478018138191875095 16634828217027207287812643)
                ·
                  refine ⟨24952242325540810931718965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16634828217027207287812643 24952242325540810931718965)
                  ·
                    refine ⟨2339272718019451024848653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24952242325540810931718965 2339272718019451024848653)
                    ·
                      refine ⟨877227269257294134318245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2339272718019451024848653 877227269257294134318245)
                      ·
                        rfl

theorem cell23_1708394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1708394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708394 prefixEnd_1708394 := by exact prefixLift 1708394
  have htrace : WordTrace (prefixWord ++ tailWord_1708394) baseStart_1708394 baseEnd_1708394 := by
    simpa [prefixWord, tailWord_1708394, baseEnd_1708394] using wordTrace_append hprefix tailTrace_1708394
  have hstable : (prefixWord ++ tailWord_1708394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708394).length < 2 ^ (prefixWord ++ tailWord_1708394).sum := by decide
  have hdescent : baseEnd_1708394 < baseStart_1708394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708397 : List Nat := [1, 5, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_1708397 : Nat := 118140960795 + 1708397 * 2 ^ 59
def prefixEnd_1708397 : Nat := 4983230072969 + 3 ^ 40 * 1708397 * 2
def baseEnd_1708397 : Nat := 292409603233085874193577

theorem tailTrace_1708397 : CollatzResearch.WordTrace tailWord_1708397 prefixEnd_1708397 292409603233085874193577 := by
  unfold tailWord_1708397
  simp only [CollatzResearch.WordTrace]
  refine ⟨62310357591776914823635445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41540238394517943215756963 62310357591776914823635445)
  ·
    refine ⟨5841596024229085764715823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62310357591776914823635445 5841596024229085764715823)
    ·
      refine ⟨8762394036343628647073735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841596024229085764715823 8762394036343628647073735)
      ·
        refine ⟨13143591054515442970610603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762394036343628647073735 13143591054515442970610603)
        ·
          refine ⟨19715386581773164455915905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13143591054515442970610603 19715386581773164455915905)
          ·
            refine ⟨14786539936329873341936929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19715386581773164455915905 14786539936329873341936929)
            ·
              refine ⟨11089904952247405006452697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14786539936329873341936929 11089904952247405006452697)
              ·
                refine ⟨8317428714185553754839523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11089904952247405006452697 8317428714185553754839523)
                ·
                  refine ⟨12476143071278330632259285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317428714185553754839523 12476143071278330632259285)
                  ·
                    refine ⟨292409603233085874193577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12476143071278330632259285 292409603233085874193577)
                    ·
                      rfl

theorem cell23_1708397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_1708397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708397 prefixEnd_1708397 := by exact prefixLift 1708397
  have htrace : WordTrace (prefixWord ++ tailWord_1708397) baseStart_1708397 baseEnd_1708397 := by
    simpa [prefixWord, tailWord_1708397, baseEnd_1708397] using wordTrace_append hprefix tailTrace_1708397
  have hstable : (prefixWord ++ tailWord_1708397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708397).length < 2 ^ (prefixWord ++ tailWord_1708397).sum := by decide
  have hdescent : baseEnd_1708397 < baseStart_1708397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708447 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1708447 : Nat := 118140960795 + 1708447 * 2 ^ 59
def prefixEnd_1708447 : Nat := 4983230072969 + 3 ^ 40 * 1708447 * 2
def baseEnd_1708447 : Nat := 877254483731982426955501

theorem tailTrace_1708447 : CollatzResearch.WordTrace tailWord_1708447 prefixEnd_1708447 877254483731982426955501 := by
  unfold tailWord_1708447
  simp only [CollatzResearch.WordTrace]
  refine ⟨62312181241595773362955595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41541454161063848908637063 62312181241595773362955595)
  ·
    refine ⟨93468271862393660044433393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62312181241595773362955595 93468271862393660044433393)
    ·
      refine ⟨70101203896795245033325045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93468271862393660044433393 70101203896795245033325045)
      ·
        refine ⟨6571987865324554221874223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70101203896795245033325045 6571987865324554221874223)
        ·
          refine ⟨9857981797986831332811335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571987865324554221874223 9857981797986831332811335)
          ·
            refine ⟨14786972696980246999217003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857981797986831332811335 14786972696980246999217003)
            ·
              refine ⟨22180459045470370498825505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14786972696980246999217003 22180459045470370498825505)
              ·
                refine ⟨16635344284102777874119129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22180459045470370498825505 16635344284102777874119129)
                ·
                  refine ⟨12476508213077083405589347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16635344284102777874119129 12476508213077083405589347)
                  ·
                    refine ⟨18714762319615625108384021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12476508213077083405589347 18714762319615625108384021)
                    ·
                      refine ⟨877254483731982426955501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18714762319615625108384021 877254483731982426955501)
                      ·
                        rfl

theorem cell23_1708447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1708447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708447 prefixEnd_1708447 := by exact prefixLift 1708447
  have htrace : WordTrace (prefixWord ++ tailWord_1708447) baseStart_1708447 baseEnd_1708447 := by
    simpa [prefixWord, tailWord_1708447, baseEnd_1708447] using wordTrace_append hprefix tailTrace_1708447
  have hstable : (prefixWord ++ tailWord_1708447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708447).length < 2 ^ (prefixWord ++ tailWord_1708447).sum := by decide
  have hdescent : baseEnd_1708447 < baseStart_1708447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708457 : List Nat := [1, 2, 1, 1, 1, 1, 3, 7, 6]
def baseStart_1708457 : Nat := 118140960795 + 1708457 * 2 ^ 59
def prefixEnd_1708457 : Nat := 4983230072969 + 3 ^ 40 * 1708457 * 2
def baseEnd_1708457 : Nat := 97473290948725265314495

theorem tailTrace_1708457 : CollatzResearch.WordTrace tailWord_1708457 prefixEnd_1708457 97473290948725265314495 := by
  unfold tailWord_1708457
  simp only [CollatzResearch.WordTrace]
  refine ⟨62312545971559545070819625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41541697314373030047213083 62312545971559545070819625)
  ·
    refine ⟨46734409478669658803114719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62312545971559545070819625 46734409478669658803114719)
    ·
      refine ⟨70101614218004488204672079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46734409478669658803114719 70101614218004488204672079)
      ·
        refine ⟨105152421327006732307008119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70101614218004488204672079 105152421327006732307008119)
        ·
          refine ⟨157728631990510098460512179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105152421327006732307008119 157728631990510098460512179)
          ·
            refine ⟨236592947985765147690768269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157728631990510098460512179 236592947985765147690768269)
            ·
              refine ⟨88722355494661930384038101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236592947985765147690768269 88722355494661930384038101)
              ·
                refine ⟨2079430206906138993375893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88722355494661930384038101 2079430206906138993375893)
                ·
                  refine ⟨97473290948725265314495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2079430206906138993375893 97473290948725265314495)
                  ·
                    rfl

theorem cell23_1708457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 6].length) (baseStart_1708457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708457 prefixEnd_1708457 := by exact prefixLift 1708457
  have htrace : WordTrace (prefixWord ++ tailWord_1708457) baseStart_1708457 baseEnd_1708457 := by
    simpa [prefixWord, tailWord_1708457, baseEnd_1708457] using wordTrace_append hprefix tailTrace_1708457
  have hstable : (prefixWord ++ tailWord_1708457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708457).length < 2 ^ (prefixWord ++ tailWord_1708457).sum := by decide
  have hdescent : baseEnd_1708457 < baseStart_1708457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708478 : List Nat := [4, 2, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_1708478 : Nat := 118140960795 + 1708478 * 2 ^ 59
def prefixEnd_1708478 : Nat := 4983230072969 + 3 ^ 40 * 1708478 * 2
def baseEnd_1708478 : Nat := 292423467210757268555953

theorem tailTrace_1708478 : CollatzResearch.WordTrace tailWord_1708478 prefixEnd_1708478 292423467210757268555953 := by
  unfold tailWord_1708478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7789163988060433207166761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41542207936322310438222725 7789163988060433207166761)
  ·
    refine ⟨5841872991045324905375071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7789163988060433207166761 5841872991045324905375071)
    ·
      refine ⟨8762809486567987358062607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841872991045324905375071 8762809486567987358062607)
      ·
        refine ⟨13144214229851981037093911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8762809486567987358062607 13144214229851981037093911)
        ·
          refine ⟨19716321344777971555640867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13144214229851981037093911 19716321344777971555640867)
          ·
            refine ⟨29574482017166957333461301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19716321344777971555640867 29574482017166957333461301)
            ·
              refine ⟨2772607689109402250011997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29574482017166957333461301 2772607689109402250011997)
              ·
                refine ⟨1039727883416025843754499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2772607689109402250011997 1039727883416025843754499)
                ·
                  refine ⟨1559591825124038765631749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1039727883416025843754499 1559591825124038765631749)
                  ·
                    refine ⟨292423467210757268555953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559591825124038765631749 292423467210757268555953)
                    ·
                      rfl

theorem cell23_1708478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_1708478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708478 prefixEnd_1708478 := by exact prefixLift 1708478
  have htrace : WordTrace (prefixWord ++ tailWord_1708478) baseStart_1708478 baseEnd_1708478 := by
    simpa [prefixWord, tailWord_1708478, baseEnd_1708478] using wordTrace_append hprefix tailTrace_1708478
  have hstable : (prefixWord ++ tailWord_1708478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708478).length < 2 ^ (prefixWord ++ tailWord_1708478).sum := by decide
  have hdescent : baseEnd_1708478 < baseStart_1708478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708524 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_1708524 : Nat := 118140960795 + 1708524 * 2 ^ 59
def prefixEnd_1708524 : Nat := 4983230072969 + 3 ^ 40 * 1708524 * 2
def baseEnd_1708524 : Nat := 877294021742378625692647

theorem tailTrace_1708524 : CollatzResearch.WordTrace tailWord_1708524 prefixEnd_1708524 877294021742378625692647 := by
  unfold tailWord_1708524
  simp only [CollatzResearch.WordTrace]
  refine ⟨31157494831158407756754313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41543326441544543675672417 31157494831158407756754313)
  ·
    refine ⟨23368121123368805817565735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31157494831158407756754313 23368121123368805817565735)
    ·
      refine ⟨35052181685053208726348603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23368121123368805817565735 35052181685053208726348603)
      ·
        refine ⟨52578272527579813089522905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35052181685053208726348603 52578272527579813089522905)
        ·
          refine ⟨39433704395684859817142179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52578272527579813089522905 39433704395684859817142179)
          ·
            refine ⟨59150556593527289725713269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39433704395684859817142179 59150556593527289725713269)
            ·
              refine ⟨5545364680643183411785619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59150556593527289725713269 5545364680643183411785619)
              ·
                refine ⟨8318047020964775117678429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545364680643183411785619 8318047020964775117678429)
                ·
                  refine ⟨3119267632861790669129411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8318047020964775117678429 3119267632861790669129411)
                  ·
                    refine ⟨4678901449292686003694117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3119267632861790669129411 4678901449292686003694117)
                    ·
                      refine ⟨877294021742378625692647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4678901449292686003694117 877294021742378625692647)
                      ·
                        rfl

theorem cell23_1708524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_1708524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708524 prefixEnd_1708524 := by exact prefixLift 1708524
  have htrace : WordTrace (prefixWord ++ tailWord_1708524) baseStart_1708524 baseEnd_1708524 := by
    simpa [prefixWord, tailWord_1708524, baseEnd_1708524] using wordTrace_append hprefix tailTrace_1708524
  have hstable : (prefixWord ++ tailWord_1708524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708524).length < 2 ^ (prefixWord ++ tailWord_1708524).sum := by decide
  have hdescent : baseEnd_1708524 < baseStart_1708524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708554 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_1708554 : Nat := 118140960795 + 1708554 * 2 ^ 59
def prefixEnd_1708554 : Nat := 4983230072969 + 3 ^ 40 * 1708554 * 2
def baseEnd_1708554 : Nat := 877309426162013508317509

theorem tailTrace_1708554 : CollatzResearch.WordTrace tailWord_1708554 prefixEnd_1708554 877309426162013508317509 := by
  unfold tailWord_1708554
  simp only [CollatzResearch.WordTrace]
  refine ⟨15579020963052032659275179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41544055901472087091400477 15579020963052032659275179)
  ·
    refine ⟨23368531444578048988912769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15579020963052032659275179 23368531444578048988912769)
    ·
      refine ⟨17526398583433536741684577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23368531444578048988912769 17526398583433536741684577)
      ·
        refine ⟨13144798937575152556263433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17526398583433536741684577 13144798937575152556263433)
        ·
          refine ⟨9858599203181364417197575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13144798937575152556263433 9858599203181364417197575)
          ·
            refine ⟨14787898804772046625796363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858599203181364417197575 14787898804772046625796363)
            ·
              refine ⟨22181848207158069938694545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14787898804772046625796363 22181848207158069938694545)
              ·
                refine ⟨16636386155368552454020909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22181848207158069938694545 16636386155368552454020909)
                ·
                  refine ⟨6238644808263207170257841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16636386155368552454020909 6238644808263207170257841)
                  ·
                    refine ⟨4678983606197405377693381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6238644808263207170257841 4678983606197405377693381)
                    ·
                      refine ⟨877309426162013508317509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4678983606197405377693381 877309426162013508317509)
                      ·
                        rfl

theorem cell23_1708554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_1708554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708554 prefixEnd_1708554 := by exact prefixLift 1708554
  have htrace : WordTrace (prefixWord ++ tailWord_1708554) baseStart_1708554 baseEnd_1708554 := by
    simpa [prefixWord, tailWord_1708554, baseEnd_1708554] using wordTrace_append hprefix tailTrace_1708554
  have hstable : (prefixWord ++ tailWord_1708554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708554).length < 2 ^ (prefixWord ++ tailWord_1708554).sum := by decide
  have hdescent : baseEnd_1708554 < baseStart_1708554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708589 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1708589 : Nat := 118140960795 + 1708589 * 2 ^ 59
def prefixEnd_1708589 : Nat := 4983230072969 + 3 ^ 40 * 1708589 * 2
def baseEnd_1708589 : Nat := 292442465994973623793283

theorem tailTrace_1708589 : CollatzResearch.WordTrace tailWord_1708589 prefixEnd_1708589 292442465994973623793283 := by
  unfold tailWord_1708589
  simp only [CollatzResearch.WordTrace]
  refine ⟨62317360407081331614624821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41544906938054221076416547 62317360407081331614624821)
  ·
    refine ⟨5842252538163874838871077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62317360407081331614624821 5842252538163874838871077)
    ·
      refine ⟨1095422350905726532288327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5842252538163874838871077 1095422350905726532288327)
      ·
        refine ⟨1643133526358589798432491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095422350905726532288327 1643133526358589798432491)
        ·
          refine ⟨2464700289537884697648737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643133526358589798432491 2464700289537884697648737)
          ·
            refine ⟨1848525217153413523236553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2464700289537884697648737 1848525217153413523236553)
            ·
              refine ⟨1386393912865060142427415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848525217153413523236553 1386393912865060142427415)
              ·
                refine ⟨2079590869297590213641123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386393912865060142427415 2079590869297590213641123)
                ·
                  refine ⟨3119386303946385320461685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079590869297590213641123 3119386303946385320461685)
                  ·
                    refine ⟨292442465994973623793283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3119386303946385320461685 292442465994973623793283)
                    ·
                      rfl

theorem cell23_1708589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1708589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708589 prefixEnd_1708589 := by exact prefixLift 1708589
  have htrace : WordTrace (prefixWord ++ tailWord_1708589) baseStart_1708589 baseEnd_1708589 := by
    simpa [prefixWord, tailWord_1708589, baseEnd_1708589] using wordTrace_append hprefix tailTrace_1708589
  have hstable : (prefixWord ++ tailWord_1708589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708589).length < 2 ^ (prefixWord ++ tailWord_1708589).sum := by decide
  have hdescent : baseEnd_1708589 < baseStart_1708589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708608 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3]
def baseStart_1708608 : Nat := 118140960795 + 1708608 * 2 ^ 59
def prefixEnd_1708608 : Nat := 4983230072969 + 3 ^ 40 * 1708608 * 2
def baseEnd_1708608 : Nat := 877337154117356297042261

theorem tailTrace_1708608 : CollatzResearch.WordTrace tailWord_1708608 prefixEnd_1708608 877337154117356297042261 := by
  unfold tailWord_1708608
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159026697006248929783239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41545368929341665239710985 31159026697006248929783239)
  ·
    refine ⟨46738540045509373394674859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31159026697006248929783239 46738540045509373394674859)
    ·
      refine ⟨70107810068264060092012289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46738540045509373394674859 70107810068264060092012289)
      ·
        refine ⟨52580857551198045069009217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70107810068264060092012289 52580857551198045069009217)
        ·
          refine ⟨39435643163398533801756913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52580857551198045069009217 39435643163398533801756913)
          ·
            refine ⟨29576732372548900351317685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39435643163398533801756913 29576732372548900351317685)
            ·
              refine ⟨2772818659926459407936033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29576732372548900351317685 2772818659926459407936033)
              ·
                refine ⟨2079613994944844555952025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772818659926459407936033 2079613994944844555952025)
                ·
                  refine ⟨1559710496208633416964019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079613994944844555952025 1559710496208633416964019)
                  ·
                    refine ⟨2339565744312950125446029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1559710496208633416964019 2339565744312950125446029)
                    ·
                      refine ⟨877337154117356297042261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2339565744312950125446029 877337154117356297042261)
                      ·
                        rfl

theorem cell23_1708608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_1708608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708608 prefixEnd_1708608 := by exact prefixLift 1708608
  have htrace : WordTrace (prefixWord ++ tailWord_1708608) baseStart_1708608 baseEnd_1708608 := by
    simpa [prefixWord, tailWord_1708608, baseEnd_1708608] using wordTrace_append hprefix tailTrace_1708608
  have hstable : (prefixWord ++ tailWord_1708608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708608).length < 2 ^ (prefixWord ++ tailWord_1708608).sum := by decide
  have hdescent : baseEnd_1708608 < baseStart_1708608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708625 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 2, 1, 3]
def baseStart_1708625 : Nat := 118140960795 + 1708625 * 2 ^ 59
def prefixEnd_1708625 : Nat := 4983230072969 + 3 ^ 40 * 1708625 * 2
def baseEnd_1708625 : Nat := 877345883288482730529683

theorem tailTrace_1708625 : CollatzResearch.WordTrace tailWord_1708625 prefixEnd_1708625 877345883288482730529683 := by
  unfold tailWord_1708625
  simp only [CollatzResearch.WordTrace]
  refine ⟨62318673434950909762935329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41545782289967273175290219 62318673434950909762935329)
  ·
    refine ⟨46739005076213182322201497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62318673434950909762935329 46739005076213182322201497)
    ·
      refine ⟨35054253807159886741651123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46739005076213182322201497 35054253807159886741651123)
      ·
        refine ⟨52581380710739830112476685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35054253807159886741651123 52581380710739830112476685)
        ·
          refine ⟨19718017766527436292178757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52581380710739830112476685 19718017766527436292178757)
          ·
            refine ⟨3697128331223894304783517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19718017766527436292178757 3697128331223894304783517)
            ·
              refine ⟨1386423124208960364293819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3697128331223894304783517 1386423124208960364293819)
              ·
                refine ⟨2079634686313440546440729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386423124208960364293819 2079634686313440546440729)
                ·
                  refine ⟨1559726014735080409830547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079634686313440546440729 1559726014735080409830547)
                  ·
                    refine ⟨2339589022102620614745821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1559726014735080409830547 2339589022102620614745821)
                    ·
                      refine ⟨877345883288482730529683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2339589022102620614745821 877345883288482730529683)
                      ·
                        rfl

theorem cell23_1708625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 2, 1, 3].length) (baseStart_1708625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708625 prefixEnd_1708625 := by exact prefixLift 1708625
  have htrace : WordTrace (prefixWord ++ tailWord_1708625) baseStart_1708625 baseEnd_1708625 := by
    simpa [prefixWord, tailWord_1708625, baseEnd_1708625] using wordTrace_append hprefix tailTrace_1708625
  have hstable : (prefixWord ++ tailWord_1708625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708625).length < 2 ^ (prefixWord ++ tailWord_1708625).sum := by decide
  have hdescent : baseEnd_1708625 < baseStart_1708625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708682 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_1708682 : Nat := 118140960795 + 1708682 * 2 ^ 59
def prefixEnd_1708682 : Nat := 4983230072969 + 3 ^ 40 * 1708682 * 2
def baseEnd_1708682 : Nat := 877375151685789007516921

theorem tailTrace_1708682 : CollatzResearch.WordTrace tailWord_1708682 prefixEnd_1708682 877375151685789007516921 := by
  unfold tailWord_1708682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580188098936102124440075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41547168263829605665173533 15580188098936102124440075)
  ·
    refine ⟨23370282148404153186660113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15580188098936102124440075 23370282148404153186660113)
    ·
      refine ⟨17527711611303114889995085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23370282148404153186660113 17527711611303114889995085)
      ·
        refine ⟨6572891854238668083748157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17527711611303114889995085 6572891854238668083748157)
        ·
          refine ⟨2464834445339500531405559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6572891854238668083748157 2464834445339500531405559)
          ·
            refine ⟨3697251668009250797108339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464834445339500531405559 3697251668009250797108339)
            ·
              refine ⟨5545877502013876195662509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697251668009250797108339 5545877502013876195662509)
              ·
                refine ⟨2079704063255203573373441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5545877502013876195662509 2079704063255203573373441)
                ·
                  refine ⟨1559778047441402680030081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2079704063255203573373441 1559778047441402680030081)
                  ·
                    refine ⟨1169833535581052010022561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1559778047441402680030081 1169833535581052010022561)
                    ·
                      refine ⟨877375151685789007516921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169833535581052010022561 877375151685789007516921)
                      ·
                        rfl

theorem cell23_1708682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_1708682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708682 prefixEnd_1708682 := by exact prefixLift 1708682
  have htrace : WordTrace (prefixWord ++ tailWord_1708682) baseStart_1708682 baseEnd_1708682 := by
    simpa [prefixWord, tailWord_1708682, baseEnd_1708682] using wordTrace_append hprefix tailTrace_1708682
  have hstable : (prefixWord ++ tailWord_1708682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708682).length < 2 ^ (prefixWord ++ tailWord_1708682).sum := by decide
  have hdescent : baseEnd_1708682 < baseStart_1708682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708684 : List Nat := [2, 2, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_1708684 : Nat := 118140960795 + 1708684 * 2 ^ 59
def prefixEnd_1708684 : Nat := 4983230072969 + 3 ^ 40 * 1708684 * 2
def baseEnd_1708684 : Nat := 292458726215699333230637

theorem tailTrace_1708684 : CollatzResearch.WordTrace tailWord_1708684 prefixEnd_1708684 292458726215699333230637 := by
  unfold tailWord_1708684
  simp only [CollatzResearch.WordTrace]
  refine ⟨31160412670868581419666553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41547216894491441892888737 31160412670868581419666553)
  ·
    refine ⟨23370309503151436064749915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31160412670868581419666553 23370309503151436064749915)
    ·
      refine ⟨35055464254727154097124873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23370309503151436064749915 35055464254727154097124873)
      ·
        refine ⟨26291598191045365572843655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35055464254727154097124873 26291598191045365572843655)
        ·
          refine ⟨39437397286568048359265483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26291598191045365572843655 39437397286568048359265483)
          ·
            refine ⟨59156095929852072538898225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39437397286568048359265483 59156095929852072538898225)
            ·
              refine ⟨44367071947389054404173669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59156095929852072538898225 44367071947389054404173669)
              ·
                refine ⟨8318825990135447700782563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44367071947389054404173669 8318825990135447700782563)
                ·
                  refine ⟨12478238985203171551173845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8318825990135447700782563 12478238985203171551173845)
                  ·
                    refine ⟨292458726215699333230637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12478238985203171551173845 292458726215699333230637)
                    ·
                      rfl

theorem cell23_1708684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_1708684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708684 prefixEnd_1708684 := by exact prefixLift 1708684
  have htrace : WordTrace (prefixWord ++ tailWord_1708684) baseStart_1708684 baseEnd_1708684 := by
    simpa [prefixWord, tailWord_1708684, baseEnd_1708684] using wordTrace_append hprefix tailTrace_1708684
  have hstable : (prefixWord ++ tailWord_1708684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708684).length < 2 ^ (prefixWord ++ tailWord_1708684).sum := by decide
  have hdescent : baseEnd_1708684 < baseStart_1708684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708691 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 2, 5, 2]
def baseStart_1708691 : Nat := 118140960795 + 1708691 * 2 ^ 59
def prefixEnd_1708691 : Nat := 4983230072969 + 3 ^ 40 * 1708691 * 2
def baseEnd_1708691 : Nat := 877379773011679472304379

theorem tailTrace_1708691 : CollatzResearch.WordTrace tailWord_1708691 prefixEnd_1708691 877379773011679472304379 := by
  unfold tailWord_1708691
  simp only [CollatzResearch.WordTrace]
  refine ⟨62321080652711803034837927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41547387101807868689891951 62321080652711803034837927)
  ·
    refine ⟨93481620979067704552256891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62321080652711803034837927 93481620979067704552256891)
    ·
      refine ⟨140222431468601556828385337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93481620979067704552256891 140222431468601556828385337)
      ·
        refine ⟨105166823601451167621289003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140222431468601556828385337 105166823601451167621289003)
        ·
          refine ⟨157750235402176751431933505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105166823601451167621289003 157750235402176751431933505)
          ·
            refine ⟨118312676551632563573950129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157750235402176751431933505 118312676551632563573950129)
            ·
              refine ⟨88734507413724422680462597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118312676551632563573950129 88734507413724422680462597)
              ·
                refine ⟨16637720140073329252586737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88734507413724422680462597 16637720140073329252586737)
                ·
                  refine ⟨12478290105054996939440053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16637720140073329252586737 12478290105054996939440053)
                  ·
                    refine ⟨1169839697348905963072505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12478290105054996939440053 1169839697348905963072505)
                    ·
                      refine ⟨877379773011679472304379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1169839697348905963072505 877379773011679472304379)
                      ·
                        rfl

theorem cell23_1708691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 2, 5, 2].length) (baseStart_1708691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708691 prefixEnd_1708691 := by exact prefixLift 1708691
  have htrace : WordTrace (prefixWord ++ tailWord_1708691) baseStart_1708691 baseEnd_1708691 := by
    simpa [prefixWord, tailWord_1708691, baseEnd_1708691] using wordTrace_append hprefix tailTrace_1708691
  have hstable : (prefixWord ++ tailWord_1708691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708691).length < 2 ^ (prefixWord ++ tailWord_1708691).sum := by decide
  have hdescent : baseEnd_1708691 < baseStart_1708691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708701 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1708701 : Nat := 118140960795 + 1708701 * 2 ^ 59
def prefixEnd_1708701 : Nat := 4983230072969 + 3 ^ 40 * 1708701 * 2
def baseEnd_1708701 : Nat := 292461635939408144393111

theorem tailTrace_1708701 : CollatzResearch.WordTrace tailWord_1708701 prefixEnd_1708701 292461635939408144393111 := by
  unfold tailWord_1708701
  simp only [CollatzResearch.WordTrace]
  refine ⟨62321445382675574742701957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41547630255117049828467971 62321445382675574742701957)
  ·
    refine ⟨11685271009251670264256617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62321445382675574742701957 11685271009251670264256617)
    ·
      refine ⟨8763953256938752698192463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11685271009251670264256617 8763953256938752698192463)
      ·
        refine ⟨13145929885408129047288695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8763953256938752698192463 13145929885408129047288695)
        ·
          refine ⟨19718894828112193570933043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13145929885408129047288695 19718894828112193570933043)
          ·
            refine ⟨29578342242168290356399565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19718894828112193570933043 29578342242168290356399565)
            ·
              refine ⟨11091878340813108883649837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29578342242168290356399565 11091878340813108883649837)
              ·
                refine ⟨4159454377804915831368689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11091878340813108883649837 4159454377804915831368689)
                ·
                  refine ⟨3119590783353686873526517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4159454377804915831368689 3119590783353686873526517)
                  ·
                    refine ⟨292461635939408144393111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3119590783353686873526517 292461635939408144393111)
                    ·
                      rfl

theorem cell23_1708701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1708701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708701 prefixEnd_1708701 := by exact prefixLift 1708701
  have htrace : WordTrace (prefixWord ++ tailWord_1708701) baseStart_1708701 baseEnd_1708701 := by
    simpa [prefixWord, tailWord_1708701, baseEnd_1708701] using wordTrace_append hprefix tailTrace_1708701
  have hstable : (prefixWord ++ tailWord_1708701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708701).length < 2 ^ (prefixWord ++ tailWord_1708701).sum := by decide
  have hdescent : baseEnd_1708701 < baseStart_1708701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708748 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_1708748 : Nat := 118140960795 + 1708748 * 2 ^ 59
def prefixEnd_1708748 : Nat := 4983230072969 + 3 ^ 40 * 1708748 * 2
def baseEnd_1708748 : Nat := 292469680469661916430539

theorem tailTrace_1708748 : CollatzResearch.WordTrace tailWord_1708748 prefixEnd_1708748 292469680469661916430539 := by
  unfold tailWord_1708748
  simp only [CollatzResearch.WordTrace]
  refine ⟨31161579806752650884831449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41548773075670201179775265 31161579806752650884831449)
  ·
    refine ⟨23371184855064488163623587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31161579806752650884831449 23371184855064488163623587)
    ·
      refine ⟨35056777282596732245435381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23371184855064488163623587 35056777282596732245435381)
      ·
        refine ⟨3286572870243443648009567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35056777282596732245435381 3286572870243443648009567)
        ·
          refine ⟨4929859305365165472014351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286572870243443648009567 4929859305365165472014351)
          ·
            refine ⟨7394788958047748208021527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929859305365165472014351 7394788958047748208021527)
            ·
              refine ⟨11092183437071622312032291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394788958047748208021527 11092183437071622312032291)
              ·
                refine ⟨16638275155607433468048437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092183437071622312032291 16638275155607433468048437)
                ·
                  refine ⟨1559838295838196887629541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16638275155607433468048437 1559838295838196887629541)
                  ·
                    refine ⟨292469680469661916430539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1559838295838196887629541 292469680469661916430539)
                    ·
                      rfl

theorem cell23_1708748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_1708748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708748 prefixEnd_1708748 := by exact prefixLift 1708748
  have htrace : WordTrace (prefixWord ++ tailWord_1708748) baseStart_1708748 baseEnd_1708748 := by
    simpa [prefixWord, tailWord_1708748, baseEnd_1708748] using wordTrace_append hprefix tailTrace_1708748
  have hstable : (prefixWord ++ tailWord_1708748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708748).length < 2 ^ (prefixWord ++ tailWord_1708748).sum := by decide
  have hdescent : baseEnd_1708748 < baseStart_1708748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708781 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1708781 : Nat := 118140960795 + 1708781 * 2 ^ 59
def prefixEnd_1708781 : Nat := 4983230072969 + 3 ^ 40 * 1708781 * 2
def baseEnd_1708781 : Nat := 877425986270584120178965

theorem tailTrace_1708781 : CollatzResearch.WordTrace tailWord_1708781 prefixEnd_1708781 877425986270584120178965 := by
  unfold tailWord_1708781
  simp only [CollatzResearch.WordTrace]
  refine ⟨62324363222385748405614197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41549575481590498937076131 62324363222385748405614197)
  ·
    refine ⟨5842909052098663913026331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62324363222385748405614197 5842909052098663913026331)
    ·
      refine ⟨8764363578147995869539497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5842909052098663913026331 8764363578147995869539497)
      ·
        refine ⟨6573272683610996902154623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8764363578147995869539497 6573272683610996902154623)
        ·
          refine ⟨9859909025416495353231935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573272683610996902154623 9859909025416495353231935)
          ·
            refine ⟨14789863538124743029847903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9859909025416495353231935 14789863538124743029847903)
            ·
              refine ⟨22184795307187114544771855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789863538124743029847903 22184795307187114544771855)
              ·
                refine ⟨33277192960780671817157783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22184795307187114544771855 33277192960780671817157783)
                ·
                  refine ⟨49915789441171007725736675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33277192960780671817157783 49915789441171007725736675)
                  ·
                    refine ⟨74873684161756511588605013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49915789441171007725736675 74873684161756511588605013)
                    ·
                      refine ⟨877425986270584120178965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 74873684161756511588605013 877425986270584120178965)
                      ·
                        rfl

theorem cell23_1708781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1708781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708781 prefixEnd_1708781 := by exact prefixLift 1708781
  have htrace : WordTrace (prefixWord ++ tailWord_1708781) baseStart_1708781 baseEnd_1708781 := by
    simpa [prefixWord, tailWord_1708781, baseEnd_1708781] using wordTrace_append hprefix tailTrace_1708781
  have hstable : (prefixWord ++ tailWord_1708781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708781).length < 2 ^ (prefixWord ++ tailWord_1708781).sum := by decide
  have hdescent : baseEnd_1708781 < baseStart_1708781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708808 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_1708808 : Nat := 118140960795 + 1708808 * 2 ^ 59
def prefixEnd_1708808 : Nat := 4983230072969 + 3 ^ 40 * 1708808 * 2
def baseEnd_1708808 : Nat := 292479950082751838180447

theorem tailTrace_1708808 : CollatzResearch.WordTrace tailWord_1708808 prefixEnd_1708808 292479950082751838180447 := by
  unfold tailWord_1708808
  simp only [CollatzResearch.WordTrace]
  refine ⟨31162673996643966008423539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41550231995525288011231385 31162673996643966008423539)
  ·
    refine ⟨46744010994965949012635309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31162673996643966008423539 46744010994965949012635309)
    ·
      refine ⟨17529004123112230879738241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46744010994965949012635309 17529004123112230879738241)
      ·
        refine ⟨13146753092334173159803681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17529004123112230879738241 13146753092334173159803681)
        ·
          refine ⟨9860064819250629869852761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13146753092334173159803681 9860064819250629869852761)
          ·
            refine ⟨7395048614437972402389571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9860064819250629869852761 7395048614437972402389571)
            ·
              refine ⟨11092572921656958603584357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395048614437972402389571 11092572921656958603584357)
              ·
                refine ⟨2079857422810679738172067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11092572921656958603584357 2079857422810679738172067)
                ·
                  refine ⟨3119786134216019607258101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079857422810679738172067 3119786134216019607258101)
                  ·
                    refine ⟨292479950082751838180447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3119786134216019607258101 292479950082751838180447)
                    ·
                      rfl

theorem cell23_1708808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_1708808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708808 prefixEnd_1708808 := by exact prefixLift 1708808
  have htrace : WordTrace (prefixWord ++ tailWord_1708808) baseStart_1708808 baseEnd_1708808 := by
    simpa [prefixWord, tailWord_1708808, baseEnd_1708808] using wordTrace_append hprefix tailTrace_1708808
  have hstable : (prefixWord ++ tailWord_1708808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708808).length < 2 ^ (prefixWord ++ tailWord_1708808).sum := by decide
  have hdescent : baseEnd_1708808 < baseStart_1708808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708821 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_1708821 : Nat := 118140960795 + 1708821 * 2 ^ 59
def prefixEnd_1708821 : Nat := 4983230072969 + 3 ^ 40 * 1708821 * 2
def baseEnd_1708821 : Nat := 292482175165587987892927

theorem tailTrace_1708821 : CollatzResearch.WordTrace tailWord_1708821 prefixEnd_1708821 292482175165587987892927 := by
  unfold tailWord_1708821
  simp only [CollatzResearch.WordTrace]
  refine ⟨62325822142240835237070317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41550548094827223491380211 62325822142240835237070317)
  ·
    refine ⟨23372183303340313213901369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62325822142240835237070317 23372183303340313213901369)
    ·
      refine ⟨17529137477505234910426027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23372183303340313213901369 17529137477505234910426027)
      ·
        refine ⟨26293706216257852365639041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17529137477505234910426027 26293706216257852365639041)
        ·
          refine ⟨19720279662193389274229281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26293706216257852365639041 19720279662193389274229281)
          ·
            refine ⟨14790209746645041955671961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19720279662193389274229281 14790209746645041955671961)
            ·
              refine ⟨11092657309983781466753971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14790209746645041955671961 11092657309983781466753971)
              ·
                refine ⟨16638985964975672200130957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092657309983781466753971 16638985964975672200130957)
                ·
                  refine ⟨6239619736865877075049109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16638985964975672200130957 6239619736865877075049109)
                  ·
                    refine ⟨292482175165587987892927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6239619736865877075049109 292482175165587987892927)
                    ·
                      rfl

theorem cell23_1708821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_1708821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708821 prefixEnd_1708821 := by exact prefixLift 1708821
  have htrace : WordTrace (prefixWord ++ tailWord_1708821) baseStart_1708821 baseEnd_1708821 := by
    simpa [prefixWord, tailWord_1708821, baseEnd_1708821] using wordTrace_append hprefix tailTrace_1708821
  have hstable : (prefixWord ++ tailWord_1708821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708821).length < 2 ^ (prefixWord ++ tailWord_1708821).sum := by decide
  have hdescent : baseEnd_1708821 < baseStart_1708821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708841 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_1708841 : Nat := 118140960795 + 1708841 * 2 ^ 59
def prefixEnd_1708841 : Nat := 4983230072969 + 3 ^ 40 * 1708841 * 2
def baseEnd_1708841 : Nat := 877456795109853885428689

theorem tailTrace_1708841 : CollatzResearch.WordTrace tailWord_1708841 prefixEnd_1708841 877456795109853885428689 := by
  unfold tailWord_1708841
  simp only [CollatzResearch.WordTrace]
  refine ⟨62326551602168378652798377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41551034401445585768532251 62326551602168378652798377)
  ·
    refine ⟨46744913701626283989598783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62326551602168378652798377 46744913701626283989598783)
    ·
      refine ⟨70117370552439425984398175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46744913701626283989598783 70117370552439425984398175)
      ·
        refine ⟨105176055828659138976597263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70117370552439425984398175 105176055828659138976597263)
        ·
          refine ⟨157764083742988708464895895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105176055828659138976597263 157764083742988708464895895)
          ·
            refine ⟨236646125614483062697343843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157764083742988708464895895 236646125614483062697343843)
            ·
              refine ⟨354969188421724594046015765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236646125614483062697343843 354969188421724594046015765)
              ·
                refine ⟨16639180707268340345906989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 354969188421724594046015765 16639180707268340345906989)
                ·
                  refine ⟨6239692765225627629715121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16639180707268340345906989 6239692765225627629715121)
                  ·
                    refine ⟨4679769573919220722286341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239692765225627629715121 4679769573919220722286341)
                    ·
                      refine ⟨877456795109853885428689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4679769573919220722286341 877456795109853885428689)
                      ·
                        rfl

theorem cell23_1708841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_1708841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708841 prefixEnd_1708841 := by exact prefixLift 1708841
  have htrace : WordTrace (prefixWord ++ tailWord_1708841) baseStart_1708841 baseEnd_1708841 := by
    simpa [prefixWord, tailWord_1708841, baseEnd_1708841] using wordTrace_append hprefix tailTrace_1708841
  have hstable : (prefixWord ++ tailWord_1708841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708841).length < 2 ^ (prefixWord ++ tailWord_1708841).sum := by decide
  have hdescent : baseEnd_1708841 < baseStart_1708841 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708851 : List Nat := [1, 1, 1, 2, 6, 1, 1, 10]
def baseStart_1708851 : Nat := 118140960795 + 1708851 * 2 ^ 59
def prefixEnd_1708851 : Nat := 4983230072969 + 3 ^ 40 * 1708851 * 2
def baseEnd_1708851 : Nat := 32498589996903660974209

theorem tailTrace_1708851 : CollatzResearch.WordTrace tailWord_1708851 prefixEnd_1708851 32498589996903660974209 := by
  unfold tailWord_1708851
  simp only [CollatzResearch.WordTrace]
  refine ⟨62326916332132150360662407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41551277554754766907108271 62326916332132150360662407)
  ·
    refine ⟨93490374498198225540993611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62326916332132150360662407 93490374498198225540993611)
    ·
      refine ⟨140235561747297338311490417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93490374498198225540993611 140235561747297338311490417)
      ·
        refine ⟨105176671310473003733617813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140235561747297338311490417 105176671310473003733617813)
        ·
          refine ⟨4930156467678422050013335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105176671310473003733617813 4930156467678422050013335)
          ·
            refine ⟨7395234701517633075020003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930156467678422050013335 7395234701517633075020003)
            ·
              refine ⟨11092852052276449612530005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395234701517633075020003 11092852052276449612530005)
              ·
                refine ⟨32498589996903660974209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11092852052276449612530005 32498589996903660974209)
                ·
                  rfl

theorem cell23_1708851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 10].length) (baseStart_1708851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708851 prefixEnd_1708851 := by exact prefixLift 1708851
  have htrace : WordTrace (prefixWord ++ tailWord_1708851) baseStart_1708851 baseEnd_1708851 := by
    simpa [prefixWord, tailWord_1708851, baseEnd_1708851] using wordTrace_append hprefix tailTrace_1708851
  have hstable : (prefixWord ++ tailWord_1708851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708851).length < 2 ^ (prefixWord ++ tailWord_1708851).sum := by decide
  have hdescent : baseEnd_1708851 < baseStart_1708851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708882 : List Nat := [3, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_1708882 : Nat := 118140960795 + 1708882 * 2 ^ 59
def prefixEnd_1708882 : Nat := 4983230072969 + 3 ^ 40 * 1708882 * 2
def baseEnd_1708882 : Nat := 877477847816688225016001

theorem tailTrace_1708882 : CollatzResearch.WordTrace tailWord_1708882 prefixEnd_1708882 877477847816688225016001 := by
  unfold tailWord_1708882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582011748754960663760225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41552031330013228436693933 15582011748754960663760225)
  ·
    refine ⟨11686508811566220497820169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15582011748754960663760225 11686508811566220497820169)
    ·
      refine ⟨8764881608674665373365127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11686508811566220497820169 8764881608674665373365127)
      ·
        refine ⟨13147322413011998060047691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8764881608674665373365127 13147322413011998060047691)
        ·
          refine ⟨19720983619517997090071537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147322413011998060047691 19720983619517997090071537)
          ·
            refine ⟨14790737714638497817553653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19720983619517997090071537 14790737714638497817553653)
            ·
              refine ⟨1386631660747359170395655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14790737714638497817553653 1386631660747359170395655)
              ·
                refine ⟨2079947491121038755593483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386631660747359170395655 2079947491121038755593483)
                ·
                  refine ⟨3119921236681558133390225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2079947491121038755593483 3119921236681558133390225)
                  ·
                    refine ⟨2339940927511168600042669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3119921236681558133390225 2339940927511168600042669)
                    ·
                      refine ⟨877477847816688225016001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2339940927511168600042669 877477847816688225016001)
                      ·
                        rfl

theorem cell23_1708882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_1708882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708882 prefixEnd_1708882 := by exact prefixLift 1708882
  have htrace : WordTrace (prefixWord ++ tailWord_1708882) baseStart_1708882 baseEnd_1708882 := by
    simpa [prefixWord, tailWord_1708882, baseEnd_1708882] using wordTrace_append hprefix tailTrace_1708882
  have hstable : (prefixWord ++ tailWord_1708882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708882).length < 2 ^ (prefixWord ++ tailWord_1708882).sum := by decide
  have hdescent : baseEnd_1708882 < baseStart_1708882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708930 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_1708930 : Nat := 118140960795 + 1708930 * 2 ^ 59
def prefixEnd_1708930 : Nat := 4983230072969 + 3 ^ 40 * 1708930 * 2
def baseEnd_1708930 : Nat := 877502494888104037215781

theorem tailTrace_1708930 : CollatzResearch.WordTrace tailWord_1708930 prefixEnd_1708930 877502494888104037215781 := by
  unfold tailWord_1708930
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582449424711486713197061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41553198465897297901858829 15582449424711486713197061)
  ·
    refine ⟨2921709267133403758724449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15582449424711486713197061 2921709267133403758724449)
    ·
      refine ⟨2191281950350052819043337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2921709267133403758724449 2191281950350052819043337)
      ·
        refine ⟨1643461462762539614282503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191281950350052819043337 1643461462762539614282503)
        ·
          refine ⟨2465192194143809421423755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643461462762539614282503 2465192194143809421423755)
          ·
            refine ⟨3697788291215714132135633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465192194143809421423755 3697788291215714132135633)
            ·
              refine ⟨2773341218411785599101725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697788291215714132135633 2773341218411785599101725)
              ·
                refine ⟨1040002956904419599663147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773341218411785599101725 1040002956904419599663147)
                ·
                  refine ⟨1560004435356629399494721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040002956904419599663147 1560004435356629399494721)
                  ·
                    refine ⟨1170003326517472049621041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1560004435356629399494721 1170003326517472049621041)
                    ·
                      refine ⟨877502494888104037215781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170003326517472049621041 877502494888104037215781)
                      ·
                        rfl

theorem cell23_1708930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_1708930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708930 prefixEnd_1708930 := by exact prefixLift 1708930
  have htrace : WordTrace (prefixWord ++ tailWord_1708930) baseStart_1708930 baseEnd_1708930 := by
    simpa [prefixWord, tailWord_1708930, baseEnd_1708930] using wordTrace_append hprefix tailTrace_1708930
  have hstable : (prefixWord ++ tailWord_1708930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708930).length < 2 ^ (prefixWord ++ tailWord_1708930).sum := by decide
  have hdescent : baseEnd_1708930 < baseStart_1708930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708946 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_1708946 : Nat := 118140960795 + 1708946 * 2 ^ 59
def prefixEnd_1708946 : Nat := 4983230072969 + 3 ^ 40 * 1708946 * 2
def baseEnd_1708946 : Nat := 877510710578575974615707

theorem tailTrace_1708946 : CollatzResearch.WordTrace tailWord_1708946 prefixEnd_1708946 877510710578575974615707 := by
  unfold tailWord_1708946
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582595316696995396342673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41553587511191987723580461 15582595316696995396342673)
  ·
    refine ⟨11686946487522746547257005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15582595316696995396342673 11686946487522746547257005)
    ·
      refine ⟨4382604932821029955221377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11686946487522746547257005 4382604932821029955221377)
      ·
        refine ⟨3286953699615772466416033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4382604932821029955221377 3286953699615772466416033)
        ·
          refine ⟨2465215274711829349812025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3286953699615772466416033 2465215274711829349812025)
          ·
            refine ⟨1848911456033872012359019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465215274711829349812025 1848911456033872012359019)
            ·
              refine ⟨2773367184050808018538529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848911456033872012359019 2773367184050808018538529)
              ·
                refine ⟨2080025388038106013903897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2773367184050808018538529 2080025388038106013903897)
                ·
                  refine ⟨1560019041028579510427923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080025388038106013903897 1560019041028579510427923)
                  ·
                    refine ⟨2340028561542869265641885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1560019041028579510427923 2340028561542869265641885)
                    ·
                      refine ⟨877510710578575974615707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340028561542869265641885 877510710578575974615707)
                      ·
                        rfl

theorem cell23_1708946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_1708946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708946 prefixEnd_1708946 := by exact prefixLift 1708946
  have htrace : WordTrace (prefixWord ++ tailWord_1708946) baseStart_1708946 baseEnd_1708946 := by
    simpa [prefixWord, tailWord_1708946, baseEnd_1708946] using wordTrace_append hprefix tailTrace_1708946
  have hstable : (prefixWord ++ tailWord_1708946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708946).length < 2 ^ (prefixWord ++ tailWord_1708946).sum := by decide
  have hdescent : baseEnd_1708946 < baseStart_1708946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708969 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 2, 2, 2]
def baseStart_1708969 : Nat := 118140960795 + 1708969 * 2 ^ 59
def prefixEnd_1708969 : Nat := 4983230072969 + 3 ^ 40 * 1708969 * 2
def baseEnd_1708969 : Nat := 877522520633629384628101

theorem tailTrace_1708969 : CollatzResearch.WordTrace tailWord_1708969 prefixEnd_1708969 877522520633629384628101 := by
  unfold tailWord_1708969
  simp only [CollatzResearch.WordTrace]
  refine ⟨62331220145704656513457961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41554146763803104342305307 62331220145704656513457961)
  ·
    refine ⟨46748415109278492385093471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62331220145704656513457961 46748415109278492385093471)
    ·
      refine ⟨70122622663917738577640207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46748415109278492385093471 70122622663917738577640207)
      ·
        refine ⟨105183933995876607866460311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70122622663917738577640207 105183933995876607866460311)
        ·
          refine ⟨157775900993814911799690467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105183933995876607866460311 157775900993814911799690467)
          ·
            refine ⟨236663851490722367699535701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157775900993814911799690467 236663851490722367699535701)
            ·
              refine ⟨1386702254828451373239467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 236663851490722367699535701 1386702254828451373239467)
              ·
                refine ⟨2080053382242677059859201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386702254828451373239467 2080053382242677059859201)
                ·
                  refine ⟨1560040036682007794894401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080053382242677059859201 1560040036682007794894401)
                  ·
                    refine ⟨1170030027511505846170801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1560040036682007794894401 1170030027511505846170801)
                    ·
                      refine ⟨877522520633629384628101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170030027511505846170801 877522520633629384628101)
                      ·
                        rfl

theorem cell23_1708969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 2, 2, 2].length) (baseStart_1708969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708969 prefixEnd_1708969 := by exact prefixLift 1708969
  have htrace : WordTrace (prefixWord ++ tailWord_1708969) baseStart_1708969 baseEnd_1708969 := by
    simpa [prefixWord, tailWord_1708969, baseEnd_1708969] using wordTrace_append hprefix tailTrace_1708969
  have hstable : (prefixWord ++ tailWord_1708969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708969).length < 2 ^ (prefixWord ++ tailWord_1708969).sum := by decide
  have hdescent : baseEnd_1708969 < baseStart_1708969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1708992 : List Nat := [2, 1, 1, 2, 3, 5, 1, 3, 5]
def baseStart_1708992 : Nat := 118140960795 + 1708992 * 2 ^ 59
def prefixEnd_1708992 : Nat := 4983230072969 + 3 ^ 40 * 1708992 * 2
def baseEnd_1708992 : Nat := 97503814520964754960055

theorem tailTrace_1708992 : CollatzResearch.WordTrace tailWord_1708992 prefixEnd_1708992 97503814520964754960055 := by
  unfold tailWord_1708992
  simp only [CollatzResearch.WordTrace]
  refine ⟨31166029512310665720772615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41554706016414220961030153 31166029512310665720772615)
  ·
    refine ⟨46749044268465998581158923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31166029512310665720772615 46749044268465998581158923)
    ·
      refine ⟨70123566402698997871738385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46749044268465998581158923 70123566402698997871738385)
      ·
        refine ⟨52592674802024248403803789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70123566402698997871738385 52592674802024248403803789)
        ·
          refine ⟨19722253050759093151426421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52592674802024248403803789 19722253050759093151426421)
          ·
            refine ⟨1848961223508664982946227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19722253050759093151426421 1848961223508664982946227)
            ·
              refine ⟨2773441835262997474419341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848961223508664982946227 2773441835262997474419341)
              ·
                refine ⟨1040040688223624052907253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773441835262997474419341 1040040688223624052907253)
                ·
                  refine ⟨97503814520964754960055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040040688223624052907253 97503814520964754960055)
                  ·
                    rfl

theorem cell23_1708992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 3, 5].length) (baseStart_1708992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1708992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1708992 prefixEnd_1708992 := by exact prefixLift 1708992
  have htrace : WordTrace (prefixWord ++ tailWord_1708992) baseStart_1708992 baseEnd_1708992 := by
    simpa [prefixWord, tailWord_1708992, baseEnd_1708992] using wordTrace_append hprefix tailTrace_1708992
  have hstable : (prefixWord ++ tailWord_1708992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1708992).length < 2 ^ (prefixWord ++ tailWord_1708992).sum := by decide
  have hdescent : baseEnd_1708992 < baseStart_1708992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1708992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709025 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 1, 6, 2]
def baseStart_1709025 : Nat := 118140960795 + 1709025 * 2 ^ 59
def prefixEnd_1709025 : Nat := 4983230072969 + 3 ^ 40 * 1709025 * 2
def baseEnd_1709025 : Nat := 877551275550281165527843

theorem tailTrace_1709025 : CollatzResearch.WordTrace tailWord_1709025 prefixEnd_1709025 877551275550281165527843 := by
  unfold tailWord_1709025
  simp only [CollatzResearch.WordTrace]
  refine ⟨62333262633501778077496529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41555508422334518718331019 62333262633501778077496529)
  ·
    refine ⟨46749946975126333558122397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62333262633501778077496529 46749946975126333558122397)
    ·
      refine ⟨17531230115672375084295899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46749946975126333558122397 17531230115672375084295899)
      ·
        refine ⟨26296845173508562626443849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17531230115672375084295899 26296845173508562626443849)
        ·
          refine ⟨19722633880131421969832887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26296845173508562626443849 19722633880131421969832887)
          ·
            refine ⟨29583950820197132954749331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19722633880131421969832887 29583950820197132954749331)
            ·
              refine ⟨44375926230295699432123997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29583950820197132954749331 44375926230295699432123997)
              ·
                refine ⟨16640972336360887287046499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44375926230295699432123997 16640972336360887287046499)
                ·
                  refine ⟨24961458504541330930569749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16640972336360887287046499 24961458504541330930569749)
                  ·
                    refine ⟨1170068367400374887370457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24961458504541330930569749 1170068367400374887370457)
                    ·
                      refine ⟨877551275550281165527843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170068367400374887370457 877551275550281165527843)
                      ·
                        rfl

theorem cell23_1709025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6, 2].length) (baseStart_1709025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709025 prefixEnd_1709025 := by exact prefixLift 1709025
  have htrace : WordTrace (prefixWord ++ tailWord_1709025) baseStart_1709025 baseEnd_1709025 := by
    simpa [prefixWord, tailWord_1709025, baseEnd_1709025] using wordTrace_append hprefix tailTrace_1709025
  have hstable : (prefixWord ++ tailWord_1709025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709025).length < 2 ^ (prefixWord ++ tailWord_1709025).sum := by decide
  have hdescent : baseEnd_1709025 < baseStart_1709025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709112 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_1709112 : Nat := 118140960795 + 1709112 * 2 ^ 59
def prefixEnd_1709112 : Nat := 4983230072969 + 3 ^ 40 * 1709112 * 2
def baseEnd_1709112 : Nat := 292531982789074108379981

theorem tailTrace_1709112 : CollatzResearch.WordTrace tailWord_1709112 prefixEnd_1709112 292531982789074108379981 := by
  unfold tailWord_1709112
  simp only [CollatzResearch.WordTrace]
  refine ⟨31168217892093295967956795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41557623856124394623942393 31168217892093295967956795)
  ·
    refine ⟨46752326838139943951935193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31168217892093295967956795 46752326838139943951935193)
    ·
      refine ⟨35064245128604957963951395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46752326838139943951935193 35064245128604957963951395)
      ·
        refine ⟨52596367692907436945927093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35064245128604957963951395 52596367692907436945927093)
        ·
          refine ⟨4930909471210072213680665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52596367692907436945927093 4930909471210072213680665)
          ·
            refine ⟨3698182103407554160260499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4930909471210072213680665 3698182103407554160260499)
            ·
              refine ⟨5547273155111331240390749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698182103407554160260499 5547273155111331240390749)
              ·
                refine ⟨2080227433166749215146531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5547273155111331240390749 2080227433166749215146531)
                ·
                  refine ⟨3120341149750123822719797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080227433166749215146531 3120341149750123822719797)
                  ·
                    refine ⟨292531982789074108379981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3120341149750123822719797 292531982789074108379981)
                    ·
                      rfl

theorem cell23_1709112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_1709112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709112 prefixEnd_1709112 := by exact prefixLift 1709112
  have htrace : WordTrace (prefixWord ++ tailWord_1709112) baseStart_1709112 baseEnd_1709112 := by
    simpa [prefixWord, tailWord_1709112, baseEnd_1709112] using wordTrace_append hprefix tailTrace_1709112
  have hstable : (prefixWord ++ tailWord_1709112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709112).length < 2 ^ (prefixWord ++ tailWord_1709112).sum := by decide
  have hdescent : baseEnd_1709112 < baseStart_1709112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709126 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1709126 : Nat := 118140960795 + 1709126 * 2 ^ 59
def prefixEnd_1709126 : Nat := 4983230072969 + 3 ^ 40 * 1709126 * 2
def baseEnd_1709126 : Nat := 877603137096385270364879

theorem tailTrace_1709126 : CollatzResearch.WordTrace tailWord_1709126 prefixEnd_1709126 877603137096385270364879 := by
  unfold tailWord_1709126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1948029575191746010216351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41557964270757248217948821 1948029575191746010216351)
  ·
    refine ⟨2922044362787619015324527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1948029575191746010216351 2922044362787619015324527)
    ·
      refine ⟨4383066544181428522986791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922044362787619015324527 4383066544181428522986791)
      ·
        refine ⟨6574599816272142784480187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4383066544181428522986791 6574599816272142784480187)
        ·
          refine ⟨9861899724408214176720281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6574599816272142784480187 9861899724408214176720281)
          ·
            refine ⟨7396424793306160632540211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9861899724408214176720281 7396424793306160632540211)
            ·
              refine ⟨11094637189959240948810317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7396424793306160632540211 11094637189959240948810317)
              ·
                refine ⟨4160488946234715355803869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11094637189959240948810317 4160488946234715355803869)
                ·
                  refine ⟨1560183354838018258426451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4160488946234715355803869 1560183354838018258426451)
                  ·
                    refine ⟨2340275032257027387639677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1560183354838018258426451 2340275032257027387639677)
                    ·
                      refine ⟨877603137096385270364879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340275032257027387639677 877603137096385270364879)
                      ·
                        rfl

theorem cell23_1709126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1709126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709126 prefixEnd_1709126 := by exact prefixLift 1709126
  have htrace : WordTrace (prefixWord ++ tailWord_1709126) baseStart_1709126 baseEnd_1709126 := by
    simpa [prefixWord, tailWord_1709126, baseEnd_1709126] using wordTrace_append hprefix tailTrace_1709126
  have hstable : (prefixWord ++ tailWord_1709126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709126).length < 2 ^ (prefixWord ++ tailWord_1709126).sum := by decide
  have hdescent : baseEnd_1709126 < baseStart_1709126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709145 : List Nat := [1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1709145 : Nat := 118140960795 + 1709145 * 2 ^ 59
def prefixEnd_1709145 : Nat := 4983230072969 + 3 ^ 40 * 1709145 * 2
def baseEnd_1709145 : Nat := 877612893228820696027291

theorem tailTrace_1709145 : CollatzResearch.WordTrace tailWord_1709145 prefixEnd_1709145 877612893228820696027291 := by
  unfold tailWord_1709145
  simp only [CollatzResearch.WordTrace]
  refine ⟨62337639393067038571864889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41558426262044692381243259 62337639393067038571864889)
  ·
    refine ⟨46753229544800278928898667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62337639393067038571864889 46753229544800278928898667)
    ·
      refine ⟨70129844317200418393348001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46753229544800278928898667 70129844317200418393348001)
      ·
        refine ⟨52597383237900313795011001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70129844317200418393348001 52597383237900313795011001)
        ·
          refine ⟨39448037428425235346258251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52597383237900313795011001 39448037428425235346258251)
          ·
            refine ⟨59172056142637853019387377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39448037428425235346258251 59172056142637853019387377)
            ·
              refine ⟨44379042106978389764540533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59172056142637853019387377 44379042106978389764540533)
              ·
                refine ⟨4160535197529224040425675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44379042106978389764540533 4160535197529224040425675)
                ·
                  refine ⟨6240802796293836060638513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4160535197529224040425675 6240802796293836060638513)
                  ·
                    refine ⟨4680602097220377045478885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6240802796293836060638513 4680602097220377045478885)
                    ·
                      refine ⟨877612893228820696027291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4680602097220377045478885 877612893228820696027291)
                      ·
                        rfl

theorem cell23_1709145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1709145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709145 prefixEnd_1709145 := by exact prefixLift 1709145
  have htrace : WordTrace (prefixWord ++ tailWord_1709145) baseStart_1709145 baseEnd_1709145 := by
    simpa [prefixWord, tailWord_1709145, baseEnd_1709145] using wordTrace_append hprefix tailTrace_1709145
  have hstable : (prefixWord ++ tailWord_1709145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709145).length < 2 ^ (prefixWord ++ tailWord_1709145).sum := by decide
  have hdescent : baseEnd_1709145 < baseStart_1709145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709160 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_1709160 : Nat := 118140960795 + 1709160 * 2 ^ 59
def prefixEnd_1709160 : Nat := 4983230072969 + 3 ^ 40 * 1709160 * 2
def baseEnd_1709160 : Nat := 877620595438638137339723

theorem tailTrace_1709160 : CollatzResearch.WordTrace tailWord_1709160 prefixEnd_1709160 877620595438638137339723 := by
  unfold tailWord_1709160
  simp only [CollatzResearch.WordTrace]
  refine ⟨31169093244006348066830467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41558790992008464089107289 31169093244006348066830467)
  ·
    refine ⟨46753639866009522100245701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31169093244006348066830467 46753639866009522100245701)
    ·
      refine ⟨8766307474876785393796069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46753639866009522100245701 8766307474876785393796069)
      ·
        refine ⟨1643682651539397261336763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8766307474876785393796069 1643682651539397261336763)
        ·
          refine ⟨2465523977309095892005145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643682651539397261336763 2465523977309095892005145)
          ·
            refine ⟨1849142982981821919003859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465523977309095892005145 1849142982981821919003859)
            ·
              refine ⟨2773714474472732878505789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849142982981821919003859 2773714474472732878505789)
              ·
                refine ⟨1040142927927274829439671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773714474472732878505789 1040142927927274829439671)
                ·
                  refine ⟨1560214391890912244159507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040142927927274829439671 1560214391890912244159507)
                  ·
                    refine ⟨2340321587836368366239261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1560214391890912244159507 2340321587836368366239261)
                    ·
                      refine ⟨877620595438638137339723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340321587836368366239261 877620595438638137339723)
                      ·
                        rfl

theorem cell23_1709160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_1709160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709160 prefixEnd_1709160 := by exact prefixLift 1709160
  have htrace : WordTrace (prefixWord ++ tailWord_1709160) baseStart_1709160 baseEnd_1709160 := by
    simpa [prefixWord, tailWord_1709160, baseEnd_1709160] using wordTrace_append hprefix tailTrace_1709160
  have hstable : (prefixWord ++ tailWord_1709160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709160).length < 2 ^ (prefixWord ++ tailWord_1709160).sum := by decide
  have hdescent : baseEnd_1709160 < baseStart_1709160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709205 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_1709205 : Nat := 118140960795 + 1709205 * 2 ^ 59
def prefixEnd_1709205 : Nat := 4983230072969 + 3 ^ 40 * 1709205 * 2
def baseEnd_1709205 : Nat := 877643702068090461277015

theorem tailTrace_1709205 : CollatzResearch.WordTrace tailWord_1709205 prefixEnd_1709205 877643702068090461277015 := by
  unfold tailWord_1709205
  simp only [CollatzResearch.WordTrace]
  refine ⟨62339827772849668819049069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41559885181899779212699379 62339827772849668819049069)
  ·
    refine ⟨23377435414818625807143401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62339827772849668819049069 23377435414818625807143401)
    ·
      refine ⟨17533076561113969355357551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23377435414818625807143401 17533076561113969355357551)
      ·
        refine ⟨26299614841670954033036327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17533076561113969355357551 26299614841670954033036327)
        ·
          refine ⟨39449422262506431049554491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26299614841670954033036327 39449422262506431049554491)
          ·
            refine ⟨59174133393759646574331737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39449422262506431049554491 59174133393759646574331737)
            ·
              refine ⟨44380600045319734930748803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59174133393759646574331737 44380600045319734930748803)
              ·
                refine ⟨66570900067979602396123205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44380600045319734930748803 66570900067979602396123205)
                ·
                  refine ⟨12482043762746175449273101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66570900067979602396123205 12482043762746175449273101)
                  ·
                    refine ⟨4680766411029815793477413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12482043762746175449273101 4680766411029815793477413)
                    ·
                      refine ⟨877643702068090461277015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4680766411029815793477413 877643702068090461277015)
                      ·
                        rfl

theorem cell23_1709205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_1709205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709205 prefixEnd_1709205 := by exact prefixLift 1709205
  have htrace : WordTrace (prefixWord ++ tailWord_1709205) baseStart_1709205 baseEnd_1709205 := by
    simpa [prefixWord, tailWord_1709205, baseEnd_1709205] using wordTrace_append hprefix tailTrace_1709205
  have hstable : (prefixWord ++ tailWord_1709205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709205).length < 2 ^ (prefixWord ++ tailWord_1709205).sum := by decide
  have hdescent : baseEnd_1709205 < baseStart_1709205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709249 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 2, 6]
def baseStart_1709249 : Nat := 118140960795 + 1709249 * 2 ^ 59
def prefixEnd_1709249 : Nat := 4983230072969 + 3 ^ 40 * 1709249 * 2
def baseEnd_1709249 : Nat := 292555431738962763042271

theorem tailTrace_1709249 : CollatzResearch.WordTrace tailWord_1709249 prefixEnd_1709249 292555431738962763042271 := by
  unfold tailWord_1709249
  simp only [CollatzResearch.WordTrace]
  refine ⟨62341432584690264333650801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41560955056460176222433867 62341432584690264333650801)
  ·
    refine ⟨46756074438517698250238101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62341432584690264333650801 46756074438517698250238101)
    ·
      refine ⟨2191690989305517105479911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46756074438517698250238101 2191690989305517105479911)
      ·
        refine ⟨3287536483958275658219867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191690989305517105479911 3287536483958275658219867)
        ·
          refine ⟨4931304725937413487329801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287536483958275658219867 4931304725937413487329801)
          ·
            refine ⟨3698478544453060115497351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4931304725937413487329801 3698478544453060115497351)
            ·
              refine ⟨5547717816679590173246027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698478544453060115497351 5547717816679590173246027)
              ·
                refine ⟨8321576725019385259869041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5547717816679590173246027 8321576725019385259869041)
                ·
                  refine ⟨6241182543764538944901781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8321576725019385259869041 6241182543764538944901781)
                  ·
                    refine ⟨292555431738962763042271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6241182543764538944901781 292555431738962763042271)
                    ·
                      rfl

theorem cell23_1709249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_1709249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709249 prefixEnd_1709249 := by exact prefixLift 1709249
  have htrace : WordTrace (prefixWord ++ tailWord_1709249) baseStart_1709249 baseEnd_1709249 := by
    simpa [prefixWord, tailWord_1709249, baseEnd_1709249] using wordTrace_append hprefix tailTrace_1709249
  have hstable : (prefixWord ++ tailWord_1709249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709249).length < 2 ^ (prefixWord ++ tailWord_1709249).sum := by decide
  have hdescent : baseEnd_1709249 < baseStart_1709249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709256 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_1709256 : Nat := 118140960795 + 1709256 * 2 ^ 59
def prefixEnd_1709256 : Nat := 4983230072969 + 3 ^ 40 * 1709256 * 2
def baseEnd_1709256 : Nat := 877669889581469761739281

theorem tailTrace_1709256 : CollatzResearch.WordTrace tailWord_1709256 prefixEnd_1709256 877669889581469761739281 := by
  unfold tailWord_1709256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31170843947832452264577811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41561125263776603019437081 31170843947832452264577811)
  ·
    refine ⟨46756265921748678396866717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31170843947832452264577811 46756265921748678396866717)
    ·
      refine ⟨17533599720655754398825019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46756265921748678396866717 17533599720655754398825019)
      ·
        refine ⟨26300399580983631598237529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17533599720655754398825019 26300399580983631598237529)
        ·
          refine ⟨19725299685737723698678147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26300399580983631598237529 19725299685737723698678147)
          ·
            refine ⟨29587949528606585548017221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19725299685737723698678147 29587949528606585548017221)
            ·
              refine ⟨5547740536613734790253229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29587949528606585548017221 5547740536613734790253229)
              ·
                refine ⟨2080402701230150546344961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5547740536613734790253229 2080402701230150546344961)
                ·
                  refine ⟨1560302025922612909758721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2080402701230150546344961 1560302025922612909758721)
                  ·
                    refine ⟨1170226519441959682319041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1560302025922612909758721 1170226519441959682319041)
                    ·
                      refine ⟨877669889581469761739281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170226519441959682319041 877669889581469761739281)
                      ·
                        rfl

theorem cell23_1709256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_1709256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709256 prefixEnd_1709256 := by exact prefixLift 1709256
  have htrace : WordTrace (prefixWord ++ tailWord_1709256) baseStart_1709256 baseEnd_1709256 := by
    simpa [prefixWord, tailWord_1709256, baseEnd_1709256] using wordTrace_append hprefix tailTrace_1709256
  have hstable : (prefixWord ++ tailWord_1709256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709256).length < 2 ^ (prefixWord ++ tailWord_1709256).sum := by decide
  have hdescent : baseEnd_1709256 < baseStart_1709256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709277 : List Nat := [1, 4, 3, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_1709277 : Nat := 118140960795 + 1709277 * 2 ^ 59
def prefixEnd_1709277 : Nat := 4983230072969 + 3 ^ 40 * 1709277 * 2
def baseEnd_1709277 : Nat := 877680672675214179576685

theorem tailTrace_1709277 : CollatzResearch.WordTrace tailWord_1709277 prefixEnd_1709277 877680672675214179576685 := by
  unfold tailWord_1709277
  simp only [CollatzResearch.WordTrace]
  refine ⟨62342453828588825115670085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41561635885725883410446723 62342453828588825115670085)
  ·
    refine ⟨11689210092860404709188141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62342453828588825115670085 11689210092860404709188141)
    ·
      refine ⟨4383453784822651765945553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11689210092860404709188141 4383453784822651765945553)
      ·
        refine ⟨3287590338616988824459165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4383453784822651765945553 3287590338616988824459165)
        ·
          refine ⟨1232846376981370809172187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3287590338616988824459165 1232846376981370809172187)
          ·
            refine ⟨1849269565472056213758281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232846376981370809172187 1849269565472056213758281)
            ·
              refine ⟨1386952174104042160318711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1849269565472056213758281 1386952174104042160318711)
              ·
                refine ⟨2080428261156063240478067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386952174104042160318711 2080428261156063240478067)
                ·
                  refine ⟨3120642391734094860717101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080428261156063240478067 3120642391734094860717101)
                  ·
                    refine ⟨1170240896900285572768913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3120642391734094860717101 1170240896900285572768913)
                    ·
                      refine ⟨877680672675214179576685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170240896900285572768913 877680672675214179576685)
                      ·
                        rfl

theorem cell23_1709277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_1709277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709277 prefixEnd_1709277 := by exact prefixLift 1709277
  have htrace : WordTrace (prefixWord ++ tailWord_1709277) baseStart_1709277 baseEnd_1709277 := by
    simpa [prefixWord, tailWord_1709277, baseEnd_1709277] using wordTrace_append hprefix tailTrace_1709277
  have hstable : (prefixWord ++ tailWord_1709277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709277).length < 2 ^ (prefixWord ++ tailWord_1709277).sum := by decide
  have hdescent : baseEnd_1709277 < baseStart_1709277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709302 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1709302 : Nat := 118140960795 + 1709302 * 2 ^ 59
def prefixEnd_1709302 : Nat := 4983230072969 + 3 ^ 40 * 1709302 * 2
def baseEnd_1709302 : Nat := 877693509691576581764069

theorem tailTrace_1709302 : CollatzResearch.WordTrace tailWord_1709302 prefixEnd_1709302 877693509691576581764069 := by
  unfold tailWord_1709302
  simp only [CollatzResearch.WordTrace]
  refine ⟨3896460353343640899083135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41562243768998836256886773 3896460353343640899083135)
  ·
    refine ⟨5844690530015461348624703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3896460353343640899083135 5844690530015461348624703)
    ·
      refine ⟨8767035795023192022937055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5844690530015461348624703 8767035795023192022937055)
      ·
        refine ⟨13150553692534788034405583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767035795023192022937055 13150553692534788034405583)
        ·
          refine ⟨19725830538802182051608375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13150553692534788034405583 19725830538802182051608375)
          ·
            refine ⟨29588745808203273077412563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19725830538802182051608375 29588745808203273077412563)
            ·
              refine ⟨44383118712304909616118845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29588745808203273077412563 44383118712304909616118845)
              ·
                refine ⟨16643669517114341106044567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44383118712304909616118845 16643669517114341106044567)
                ·
                  refine ⟨24965504275671511659066851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16643669517114341106044567 24965504275671511659066851)
                  ·
                    refine ⟨37448256413507267488600277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24965504275671511659066851 37448256413507267488600277)
                    ·
                      refine ⟨877693509691576581764069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37448256413507267488600277 877693509691576581764069)
                      ·
                        rfl

theorem cell23_1709302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1709302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709302 prefixEnd_1709302 := by exact prefixLift 1709302
  have htrace : WordTrace (prefixWord ++ tailWord_1709302) baseStart_1709302 baseEnd_1709302 := by
    simpa [prefixWord, tailWord_1709302, baseEnd_1709302] using wordTrace_append hprefix tailTrace_1709302
  have hstable : (prefixWord ++ tailWord_1709302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709302).length < 2 ^ (prefixWord ++ tailWord_1709302).sum := by decide
  have hdescent : baseEnd_1709302 < baseStart_1709302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709330 : List Nat := [3, 2, 4, 2, 1, 2, 1, 3, 5]
def baseStart_1709330 : Nat := 118140960795 + 1709330 * 2 ^ 59
def prefixEnd_1709330 : Nat := 4983230072969 + 3 ^ 40 * 1709330 * 2
def baseEnd_1709330 : Nat := 97523098572211385801549

theorem tailTrace_1709330 : CollatzResearch.WordTrace tailWord_1709330 prefixEnd_1709330 97523098572211385801549 := by
  unfold tailWord_1709330
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586096724349203791837361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41562924598264543444899629 15586096724349203791837361)
  ·
    refine ⟨11689572543261902843878021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15586096724349203791837361 11689572543261902843878021)
    ·
      refine ⟨2191794851861606783227129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11689572543261902843878021 2191794851861606783227129)
      ·
        refine ⟨1643846138896205087420347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2191794851861606783227129 1643846138896205087420347)
        ·
          refine ⟨2465769208344307631130521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643846138896205087420347 2465769208344307631130521)
          ·
            refine ⟨1849326906258230723347891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465769208344307631130521 1849326906258230723347891)
            ·
              refine ⟨2773990359387346085021837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849326906258230723347891 2773990359387346085021837)
              ·
                refine ⟨1040246384770254781883189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773990359387346085021837 1040246384770254781883189)
                ·
                  refine ⟨97523098572211385801549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040246384770254781883189 97523098572211385801549)
                  ·
                    rfl

theorem cell23_1709330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 5].length) (baseStart_1709330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709330 prefixEnd_1709330 := by exact prefixLift 1709330
  have htrace : WordTrace (prefixWord ++ tailWord_1709330) baseStart_1709330 baseEnd_1709330 := by
    simpa [prefixWord, tailWord_1709330, baseEnd_1709330] using wordTrace_append hprefix tailTrace_1709330
  have hstable : (prefixWord ++ tailWord_1709330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709330).length < 2 ^ (prefixWord ++ tailWord_1709330).sum := by decide
  have hdescent : baseEnd_1709330 < baseStart_1709330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709346 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1709346 : Nat := 118140960795 + 1709346 * 2 ^ 59
def prefixEnd_1709346 : Nat := 4983230072969 + 3 ^ 40 * 1709346 * 2
def baseEnd_1709346 : Nat := 877716102840374409613867

theorem tailTrace_1709346 : CollatzResearch.WordTrace tailWord_1709346 prefixEnd_1709346 877716102840374409613867 := by
  unfold tailWord_1709346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586242616334712474982973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41563313643559233266621261 15586242616334712474982973)
  ·
    refine ⟨5844840981125517178118615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15586242616334712474982973 5844840981125517178118615)
    ·
      refine ⟨8767261471688275767177923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5844840981125517178118615 8767261471688275767177923)
      ·
        refine ⟨13150892207532413650766885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767261471688275767177923 13150892207532413650766885)
        ·
          refine ⟨2465792288912327559518791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13150892207532413650766885 2465792288912327559518791)
          ·
            refine ⟨3698688433368491339278187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465792288912327559518791 3698688433368491339278187)
            ·
              refine ⟨5548032650052737008917281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3698688433368491339278187 5548032650052737008917281)
              ·
                refine ⟨4161024487539552756687961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5548032650052737008917281 4161024487539552756687961)
                ·
                  refine ⟨3120768365654664567515971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4161024487539552756687961 3120768365654664567515971)
                  ·
                    refine ⟨4681152548481996851273957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3120768365654664567515971 4681152548481996851273957)
                    ·
                      refine ⟨877716102840374409613867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4681152548481996851273957 877716102840374409613867)
                      ·
                        rfl

theorem cell23_1709346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1709346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709346 prefixEnd_1709346 := by exact prefixLift 1709346
  have htrace : WordTrace (prefixWord ++ tailWord_1709346) baseStart_1709346 baseEnd_1709346 := by
    simpa [prefixWord, tailWord_1709346, baseEnd_1709346] using wordTrace_append hprefix tailTrace_1709346
  have hstable : (prefixWord ++ tailWord_1709346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709346).length < 2 ^ (prefixWord ++ tailWord_1709346).sum := by decide
  have hdescent : baseEnd_1709346 < baseStart_1709346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709349 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_1709349 : Nat := 118140960795 + 1709349 * 2 ^ 59
def prefixEnd_1709349 : Nat := 4983230072969 + 3 ^ 40 * 1709349 * 2
def baseEnd_1709349 : Nat := 877717643282337897876353

theorem tailTrace_1709349 : CollatzResearch.WordTrace tailWord_1709349 prefixEnd_1709349 877717643282337897876353 := by
  unfold tailWord_1709349
  simp only [CollatzResearch.WordTrace]
  refine ⟨62345079884327981412291101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41563386589551987608194067 62345079884327981412291101)
  ·
    refine ⟨23379404956622993029609163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62345079884327981412291101 23379404956622993029609163)
    ·
      refine ⟨35069107434934489544413745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23379404956622993029609163 35069107434934489544413745)
      ·
        refine ⟨26301830576200867158310309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35069107434934489544413745 26301830576200867158310309)
        ·
          refine ⟨4931593233037662592183183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26301830576200867158310309 4931593233037662592183183)
          ·
            refine ⟨7397389849556493888274775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931593233037662592183183 7397389849556493888274775)
            ·
              refine ⟨11096084774334740832412163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397389849556493888274775 11096084774334740832412163)
              ·
                refine ⟨16644127161502111248618245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11096084774334740832412163 16644127161502111248618245)
                ·
                  refine ⟨3120773842781645859115921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16644127161502111248618245 3120773842781645859115921)
                  ·
                    refine ⟨2340580382086234394336941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3120773842781645859115921 2340580382086234394336941)
                    ·
                      refine ⟨877717643282337897876353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340580382086234394336941 877717643282337897876353)
                      ·
                        rfl

theorem cell23_1709349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_1709349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709349 prefixEnd_1709349 := by exact prefixLift 1709349
  have htrace : WordTrace (prefixWord ++ tailWord_1709349) baseStart_1709349 baseEnd_1709349 := by
    simpa [prefixWord, tailWord_1709349, baseEnd_1709349] using wordTrace_append hprefix tailTrace_1709349
  have hstable : (prefixWord ++ tailWord_1709349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709349).length < 2 ^ (prefixWord ++ tailWord_1709349).sum := by decide
  have hdescent : baseEnd_1709349 < baseStart_1709349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709379 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 3]
def baseStart_1709379 : Nat := 118140960795 + 1709379 * 2 ^ 59
def prefixEnd_1709379 : Nat := 4983230072969 + 3 ^ 40 * 1709379 * 2
def baseEnd_1709379 : Nat := 877733047701972780501215

theorem tailTrace_1709379 : CollatzResearch.WordTrace tailWord_1709379 prefixEnd_1709379 877733047701972780501215 := by
  unfold tailWord_1709379
  simp only [CollatzResearch.WordTrace]
  refine ⟨62346174074219296535883191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41564116049479531023922127 62346174074219296535883191)
  ·
    refine ⟨93519261111328944803824787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62346174074219296535883191 93519261111328944803824787)
    ·
      refine ⟨140278891666993417205737181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93519261111328944803824787 140278891666993417205737181)
      ·
        refine ⟨52604584375122531452151443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140278891666993417205737181 52604584375122531452151443)
        ·
          refine ⟨78906876562683797178227165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52604584375122531452151443 78906876562683797178227165)
          ·
            refine ⟨29590078711006423941835187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78906876562683797178227165 29590078711006423941835187)
            ·
              refine ⟨44385118066509635912752781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29590078711006423941835187 44385118066509635912752781)
              ·
                refine ⟨16644419274941113467282293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44385118066509635912752781 16644419274941113467282293)
                ·
                  refine ⟨1560414307025729387557715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16644419274941113467282293 1560414307025729387557715)
                  ·
                    refine ⟨2340621460538594081336573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1560414307025729387557715 2340621460538594081336573)
                    ·
                      refine ⟨877733047701972780501215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340621460538594081336573 877733047701972780501215)
                      ·
                        rfl

theorem cell23_1709379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_1709379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709379 prefixEnd_1709379 := by exact prefixLift 1709379
  have htrace : WordTrace (prefixWord ++ tailWord_1709379) baseStart_1709379 baseEnd_1709379 := by
    simpa [prefixWord, tailWord_1709379, baseEnd_1709379] using wordTrace_append hprefix tailTrace_1709379
  have hstable : (prefixWord ++ tailWord_1709379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709379).length < 2 ^ (prefixWord ++ tailWord_1709379).sum := by decide
  have hdescent : baseEnd_1709379 < baseStart_1709379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709413 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 1, 1, 3]
def baseStart_1709413 : Nat := 118140960795 + 1709413 * 2 ^ 59
def prefixEnd_1709413 : Nat := 4983230072969 + 3 ^ 40 * 1709413 * 2
def baseEnd_1709413 : Nat := 877750506044225647476059

theorem tailTrace_1709413 : CollatzResearch.WordTrace tailWord_1709413 prefixEnd_1709413 877750506044225647476059 := by
  unfold tailWord_1709413
  simp only [CollatzResearch.WordTrace]
  refine ⟨62347414156096120342620893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41564942770730746895080595 62347414156096120342620893)
  ·
    refine ⟨23380280308536045128482835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62347414156096120342620893 23380280308536045128482835)
    ·
      refine ⟨35070420462804067692724253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23380280308536045128482835 35070420462804067692724253)
      ·
        refine ⟨13151407673551525384771595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35070420462804067692724253 13151407673551525384771595)
        ·
          refine ⟨19727111510327288077157393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13151407673551525384771595 19727111510327288077157393)
          ·
            refine ⟨14795333632745466057868045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19727111510327288077157393 14795333632745466057868045)
            ·
              refine ⟨5548250112279549771700517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14795333632745466057868045 5548250112279549771700517)
              ·
                refine ⟨1040296896052415582193847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5548250112279549771700517 1040296896052415582193847)
                ·
                  refine ⟨1560445344078623373290771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040296896052415582193847 1560445344078623373290771)
                  ·
                    refine ⟨2340668016117935059936157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1560445344078623373290771 2340668016117935059936157)
                    ·
                      refine ⟨877750506044225647476059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340668016117935059936157 877750506044225647476059)
                      ·
                        rfl

theorem cell23_1709413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_1709413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709413 prefixEnd_1709413 := by exact prefixLift 1709413
  have htrace : WordTrace (prefixWord ++ tailWord_1709413) baseStart_1709413 baseEnd_1709413 := by
    simpa [prefixWord, tailWord_1709413, baseEnd_1709413] using wordTrace_append hprefix tailTrace_1709413
  have hstable : (prefixWord ++ tailWord_1709413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709413).length < 2 ^ (prefixWord ++ tailWord_1709413).sum := by decide
  have hdescent : baseEnd_1709413 < baseStart_1709413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709480 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1709480 : Nat := 118140960795 + 1709480 * 2 ^ 59
def prefixEnd_1709480 : Nat := 4983230072969 + 3 ^ 40 * 1709480 * 2
def baseEnd_1709480 : Nat := 292594969749358961779417

theorem tailTrace_1709480 : CollatzResearch.WordTrace tailWord_1709480 prefixEnd_1709480 292594969749358961779417 := by
  unfold tailWord_1709480
  simp only [CollatzResearch.WordTrace]
  refine ⟨31174928923426695392654947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41566571897902260523539929 31174928923426695392654947)
  ·
    refine ⟨46762393385140043088982421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31174928923426695392654947 46762393385140043088982421)
    ·
      refine ⟨2191987189928439519796051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46762393385140043088982421 2191987189928439519796051)
      ·
        refine ⟨3287980784892659279694077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191987189928439519796051 3287980784892659279694077)
        ·
          refine ⟨1232992794334747229885279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3287980784892659279694077 1232992794334747229885279)
          ·
            refine ⟨1849489191502120844827919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232992794334747229885279 1849489191502120844827919)
            ·
              refine ⟨2774233787253181267241879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849489191502120844827919 2774233787253181267241879)
              ·
                refine ⟨4161350680879771900862819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774233787253181267241879 4161350680879771900862819)
                ·
                  refine ⟨6242026021319657851294229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4161350680879771900862819 6242026021319657851294229)
                  ·
                    refine ⟨292594969749358961779417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6242026021319657851294229 292594969749358961779417)
                    ·
                      rfl

theorem cell23_1709480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1709480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709480 prefixEnd_1709480 := by exact prefixLift 1709480
  have htrace : WordTrace (prefixWord ++ tailWord_1709480) baseStart_1709480 baseEnd_1709480 := by
    simpa [prefixWord, tailWord_1709480, baseEnd_1709480] using wordTrace_append hprefix tailTrace_1709480
  have hstable : (prefixWord ++ tailWord_1709480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709480).length < 2 ^ (prefixWord ++ tailWord_1709480).sum := by decide
  have hdescent : baseEnd_1709480 < baseStart_1709480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709496 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_1709496 : Nat := 118140960795 + 1709496 * 2 ^ 59
def prefixEnd_1709496 : Nat := 4983230072969 + 3 ^ 40 * 1709496 * 2
def baseEnd_1709496 : Nat := 877793124938548822738177

theorem tailTrace_1709496 : CollatzResearch.WordTrace tailWord_1709496 prefixEnd_1709496 877793124938548822738177 := by
  unfold tailWord_1709496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175220707397712758946171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41566960943196950345261561 31175220707397712758946171)
  ·
    refine ⟨46762831061096569138419257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31175220707397712758946171 46762831061096569138419257)
    ·
      refine ⟨35072123295822426853814443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46762831061096569138419257 35072123295822426853814443)
      ·
        refine ⟨52608184943733640280721665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35072123295822426853814443 52608184943733640280721665)
        ·
          refine ⟨39456138707800230210541249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52608184943733640280721665 39456138707800230210541249)
          ·
            refine ⟨29592104030850172657905937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39456138707800230210541249 29592104030850172657905937)
            ·
              refine ⟨22194078023137629493429453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29592104030850172657905937 22194078023137629493429453)
              ·
                refine ⟨8322779258676611060036045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22194078023137629493429453 8322779258676611060036045)
                ·
                  refine ⟨3121042222003729147513517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8322779258676611060036045 3121042222003729147513517)
                  ·
                    refine ⟨1170390833251398430317569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3121042222003729147513517 1170390833251398430317569)
                    ·
                      refine ⟨877793124938548822738177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170390833251398430317569 877793124938548822738177)
                      ·
                        rfl

theorem cell23_1709496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_1709496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709496 prefixEnd_1709496 := by exact prefixLift 1709496
  have htrace : WordTrace (prefixWord ++ tailWord_1709496) baseStart_1709496 baseEnd_1709496 := by
    simpa [prefixWord, tailWord_1709496, baseEnd_1709496] using wordTrace_append hprefix tailTrace_1709496
  have hstable : (prefixWord ++ tailWord_1709496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709496).length < 2 ^ (prefixWord ++ tailWord_1709496).sum := by decide
  have hdescent : baseEnd_1709496 < baseStart_1709496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709559 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_1709559 : Nat := 118140960795 + 1709559 * 2 ^ 59
def prefixEnd_1709559 : Nat := 4983230072969 + 3 ^ 40 * 1709559 * 2
def baseEnd_1709559 : Nat := 877825474219782076250387

theorem tailTrace_1709559 : CollatzResearch.WordTrace tailWord_1709559 prefixEnd_1709559 877825474219782076250387 := by
  unfold tailWord_1709559
  simp only [CollatzResearch.WordTrace]
  refine ⟨62352739213567187277435731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41568492809044791518290487 62352739213567187277435731)
  ·
    refine ⟨93529108820350780916153597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62352739213567187277435731 93529108820350780916153597)
    ·
      refine ⟨35073415807631542843557599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93529108820350780916153597 35073415807631542843557599)
      ·
        refine ⟨52610123711447314265336399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35073415807631542843557599 52610123711447314265336399)
        ·
          refine ⟨78915185567170971398004599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52610123711447314265336399 78915185567170971398004599)
          ·
            refine ⟨118372778350756457097006899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78915185567170971398004599 118372778350756457097006899)
            ·
              refine ⟨177559167526134685645510349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118372778350756457097006899 177559167526134685645510349)
              ·
                refine ⟨66584687822300507117066381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177559167526134685645510349 66584687822300507117066381)
                ·
                  refine ⟨24969257933362690168899893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66584687822300507117066381 24969257933362690168899893)
                  ·
                    refine ⟨2340867931252752203334365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24969257933362690168899893 2340867931252752203334365)
                    ·
                      refine ⟨877825474219782076250387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2340867931252752203334365 877825474219782076250387)
                      ·
                        rfl

theorem cell23_1709559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_1709559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709559 prefixEnd_1709559 := by exact prefixLift 1709559
  have htrace : WordTrace (prefixWord ++ tailWord_1709559) baseStart_1709559 baseEnd_1709559 := by
    simpa [prefixWord, tailWord_1709559, baseEnd_1709559] using wordTrace_append hprefix tailTrace_1709559
  have hstable : (prefixWord ++ tailWord_1709559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709559).length < 2 ^ (prefixWord ++ tailWord_1709559).sum := by decide
  have hdescent : baseEnd_1709559 < baseStart_1709559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709616 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2]
def baseStart_1709616 : Nat := 118140960795 + 1709616 * 2 ^ 59
def prefixEnd_1709616 : Nat := 4983230072969 + 3 ^ 40 * 1709616 * 2
def baseEnd_1709616 : Nat := 877854742617088353237625

theorem tailTrace_1709616 : CollatzResearch.WordTrace tailWord_1709616 prefixEnd_1709616 877854742617088353237625 := by
  unfold tailWord_1709616
  simp only [CollatzResearch.WordTrace]
  refine ⟨31177409087180343006130351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41569878782907124008173801 31177409087180343006130351)
  ·
    refine ⟨46766113630770514509195527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31177409087180343006130351 46766113630770514509195527)
    ·
      refine ⟨70149170446155771763793291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46766113630770514509195527 70149170446155771763793291)
      ·
        refine ⟨105223755669233657645689937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70149170446155771763793291 105223755669233657645689937)
        ·
          refine ⟨78917816751925243234267453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105223755669233657645689937 78917816751925243234267453)
          ·
            refine ⟨29594181281971966212850295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78917816751925243234267453 29594181281971966212850295)
            ·
              refine ⟨44391271922957949319275443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29594181281971966212850295 44391271922957949319275443)
              ·
                refine ⟨66586907884436923978913165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44391271922957949319275443 66586907884436923978913165)
                ·
                  refine ⟨24970090456663846492092437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66586907884436923978913165 24970090456663846492092437)
                  ·
                    refine ⟨1170472990156117804316833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24970090456663846492092437 1170472990156117804316833)
                    ·
                      refine ⟨877854742617088353237625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170472990156117804316833 877854742617088353237625)
                      ·
                        rfl

theorem cell23_1709616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 3, 6, 2].length) (baseStart_1709616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709616 prefixEnd_1709616 := by exact prefixLift 1709616
  have htrace : WordTrace (prefixWord ++ tailWord_1709616) baseStart_1709616 baseEnd_1709616 := by
    simpa [prefixWord, tailWord_1709616, baseEnd_1709616] using wordTrace_append hprefix tailTrace_1709616
  have hstable : (prefixWord ++ tailWord_1709616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709616).length < 2 ^ (prefixWord ++ tailWord_1709616).sum := by decide
  have hdescent : baseEnd_1709616 < baseStart_1709616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709626 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 5, 4]
def baseStart_1709626 : Nat := 118140960795 + 1709626 * 2 ^ 59
def prefixEnd_1709626 : Nat := 4983230072969 + 3 ^ 40 * 1709626 * 2
def baseEnd_1709626 : Nat := 292619959141211104704193

theorem tailTrace_1709626 : CollatzResearch.WordTrace tailWord_1709626 prefixEnd_1709626 292619959141211104704193 := by
  unfold tailWord_1709626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588795726081114430031183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41570121936216305146749821 15588795726081114430031183)
  ·
    refine ⟨23383193589121671645046775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588795726081114430031183 23383193589121671645046775)
    ·
      refine ⟨35074790383682507467570163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23383193589121671645046775 35074790383682507467570163)
      ·
        refine ⟨52612185575523761201355245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35074790383682507467570163 52612185575523761201355245)
        ·
          refine ⟨19729569590821410450508217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52612185575523761201355245 19729569590821410450508217)
          ·
            refine ⟨14797177193116057837881163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19729569590821410450508217 14797177193116057837881163)
            ·
              refine ⟨22195765789674086756821745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14797177193116057837881163 22195765789674086756821745)
              ·
                refine ⟨16646824342255565067616309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22195765789674086756821745 16646824342255565067616309)
                ·
                  refine ⟨1560639782086459225089029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16646824342255565067616309 1560639782086459225089029)
                  ·
                    refine ⟨292619959141211104704193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1560639782086459225089029 292619959141211104704193)
                    ·
                      rfl

theorem cell23_1709626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_1709626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709626 prefixEnd_1709626 := by exact prefixLift 1709626
  have htrace : WordTrace (prefixWord ++ tailWord_1709626) baseStart_1709626 baseEnd_1709626 := by
    simpa [prefixWord, tailWord_1709626, baseEnd_1709626] using wordTrace_append hprefix tailTrace_1709626
  have hstable : (prefixWord ++ tailWord_1709626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709626).length < 2 ^ (prefixWord ++ tailWord_1709626).sum := by decide
  have hdescent : baseEnd_1709626 < baseStart_1709626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709633 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1709633 : Nat := 118140960795 + 1709633 * 2 ^ 59
def prefixEnd_1709633 : Nat := 4983230072969 + 3 ^ 40 * 1709633 * 2
def baseEnd_1709633 : Nat := 877863471788214786725047

theorem tailTrace_1709633 : CollatzResearch.WordTrace tailWord_1709633 prefixEnd_1709633 877863471788214786725047 := by
  unfold tailWord_1709633
  simp only [CollatzResearch.WordTrace]
  refine ⟨62355438215299097915629553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41570292143532731943753035 62355438215299097915629553)
  ·
    refine ⟨46766578661474323436722165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62355438215299097915629553 46766578661474323436722165)
    ·
      refine ⟨4384366749513217822192703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46766578661474323436722165 4384366749513217822192703)
      ·
        refine ⟨6576550124269826733289055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4384366749513217822192703 6576550124269826733289055)
        ·
          refine ⟨9864825186404740099933583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576550124269826733289055 9864825186404740099933583)
          ·
            refine ⟨14797237779607110149900375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9864825186404740099933583 14797237779607110149900375)
            ·
              refine ⟨22195856669410665224850563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14797237779607110149900375 22195856669410665224850563)
              ·
                refine ⟨33293785004115997837275845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22195856669410665224850563 33293785004115997837275845)
                ·
                  refine ⟨6242584688271749594489221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33293785004115997837275845 6242584688271749594489221)
                  ·
                    refine ⟨1170484629050953048966729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6242584688271749594489221 1170484629050953048966729)
                    ·
                      refine ⟨877863471788214786725047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170484629050953048966729 877863471788214786725047)
                      ·
                        rfl

theorem cell23_1709633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1709633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709633 prefixEnd_1709633 := by exact prefixLift 1709633
  have htrace : WordTrace (prefixWord ++ tailWord_1709633) baseStart_1709633 baseEnd_1709633 := by
    simpa [prefixWord, tailWord_1709633, baseEnd_1709633] using wordTrace_append hprefix tailTrace_1709633
  have hstable : (prefixWord ++ tailWord_1709633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709633).length < 2 ^ (prefixWord ++ tailWord_1709633).sum := by decide
  have hdescent : baseEnd_1709633 < baseStart_1709633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709720 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_1709720 : Nat := 118140960795 + 1709720 * 2 ^ 59
def prefixEnd_1709720 : Nat := 4983230072969 + 3 ^ 40 * 1709720 * 2
def baseEnd_1709720 : Nat := 292636048201718648779049

theorem tailTrace_1709720 : CollatzResearch.WordTrace tailWord_1709720 prefixEnd_1709720 292636048201718648779049 := by
  unfold tailWord_1709720
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179305682991955887023307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41572407577322607849364409 31179305682991955887023307)
  ·
    refine ⟨46768958524487933830534961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31179305682991955887023307 46768958524487933830534961)
    ·
      refine ⟨35076718893365950372901221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46768958524487933830534961 35076718893365950372901221)
      ·
        refine ⟨6576884792506115694918979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35076718893365950372901221 6576884792506115694918979)
        ·
          refine ⟨9865327188759173542378469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6576884792506115694918979 9865327188759173542378469)
          ·
            refine ⟨1849748847892345039195963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9865327188759173542378469 1849748847892345039195963)
            ·
              refine ⟨2774623271838517558793945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849748847892345039195963 2774623271838517558793945)
              ·
                refine ⟨2080967453878888169095459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2774623271838517558793945 2080967453878888169095459)
                ·
                  refine ⟨3121451180818332253643189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2080967453878888169095459 3121451180818332253643189)
                  ·
                    refine ⟨292636048201718648779049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3121451180818332253643189 292636048201718648779049)
                    ·
                      rfl

theorem cell23_1709720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_1709720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709720 prefixEnd_1709720 := by exact prefixLift 1709720
  have htrace : WordTrace (prefixWord ++ tailWord_1709720) baseStart_1709720 baseEnd_1709720 := by
    simpa [prefixWord, tailWord_1709720, baseEnd_1709720] using wordTrace_append hprefix tailTrace_1709720
  have hstable : (prefixWord ++ tailWord_1709720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709720).length < 2 ^ (prefixWord ++ tailWord_1709720).sum := by decide
  have hdescent : baseEnd_1709720 < baseStart_1709720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709770 : List Nat := [3, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_1709770 : Nat := 118140960795 + 1709770 * 2 ^ 59
def prefixEnd_1709770 : Nat := 4983230072969 + 3 ^ 40 * 1709770 * 2
def baseEnd_1709770 : Nat := 877933818637880750711917

theorem tailTrace_1709770 : CollatzResearch.WordTrace tailWord_1709770 prefixEnd_1709770 877933818637880750711917 := by
  unfold tailWord_1709770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15590108753950692578341691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41573623343868513542244509 15590108753950692578341691)
  ·
    refine ⟨23385163130926038867512537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15590108753950692578341691 23385163130926038867512537)
    ·
      refine ⟨17538872348194529150634403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23385163130926038867512537 17538872348194529150634403)
      ·
        refine ⟨26308308522291793725951605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17538872348194529150634403 26308308522291793725951605)
        ·
          refine ⟨2466403923964855661807963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26308308522291793725951605 2466403923964855661807963)
          ·
            refine ⟨3699605885947283492711945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466403923964855661807963 3699605885947283492711945)
            ·
              refine ⟨2774704414460462619533959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3699605885947283492711945 2774704414460462619533959)
              ·
                refine ⟨4162056621690693929300939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774704414460462619533959 4162056621690693929300939)
                ·
                  refine ⟨6243084932536040893951409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4162056621690693929300939 6243084932536040893951409)
                  ·
                    refine ⟨4682313699402030670463557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6243084932536040893951409 4682313699402030670463557)
                    ·
                      refine ⟨877933818637880750711917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4682313699402030670463557 877933818637880750711917)
                      ·
                        rfl

theorem cell23_1709770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_1709770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709770 prefixEnd_1709770 := by exact prefixLift 1709770
  have htrace : WordTrace (prefixWord ++ tailWord_1709770) baseStart_1709770 baseEnd_1709770 := by
    simpa [prefixWord, tailWord_1709770, baseEnd_1709770] using wordTrace_append hprefix tailTrace_1709770
  have hstable : (prefixWord ++ tailWord_1709770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709770).length < 2 ^ (prefixWord ++ tailWord_1709770).sum := by decide
  have hdescent : baseEnd_1709770 < baseStart_1709770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709780 : List Nat := [2, 4, 1, 3, 1, 2, 3, 7]
def baseStart_1709780 : Nat := 118140960795 + 1709780 * 2 ^ 59
def prefixEnd_1709780 : Nat := 4983230072969 + 3 ^ 40 * 1709780 * 2
def baseEnd_1709780 : Nat := 32516257534978730058773

theorem tailTrace_1709780 : CollatzResearch.WordTrace tailWord_1709780 prefixEnd_1709780 32516257534978730058773 := by
  unfold tailWord_1709780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31180399872883271010615397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41573866497177694680820529 31180399872883271010615397)
  ·
    refine ⟨5846324976165613314490387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31180399872883271010615397 5846324976165613314490387)
    ·
      refine ⟨8769487464248419971735581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5846324976165613314490387 8769487464248419971735581)
      ·
        refine ⟨3288557799093157489400843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8769487464248419971735581 3288557799093157489400843)
        ·
          refine ⟨4932836698639736234101265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288557799093157489400843 4932836698639736234101265)
          ·
            refine ⟨3699627523979802175575949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4932836698639736234101265 3699627523979802175575949)
            ·
              refine ⟨1387360321492425815840981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3699627523979802175575949 1387360321492425815840981)
              ·
                refine ⟨32516257534978730058773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1387360321492425815840981 32516257534978730058773)
                ·
                  rfl

theorem cell23_1709780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 7].length) (baseStart_1709780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709780 prefixEnd_1709780 := by exact prefixLift 1709780
  have htrace : WordTrace (prefixWord ++ tailWord_1709780) baseStart_1709780 baseEnd_1709780 := by
    simpa [prefixWord, tailWord_1709780, baseEnd_1709780] using wordTrace_append hprefix tailTrace_1709780
  have hstable : (prefixWord ++ tailWord_1709780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709780).length < 2 ^ (prefixWord ++ tailWord_1709780).sum := by decide
  have hdescent : baseEnd_1709780 < baseStart_1709780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709816 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_1709816 : Nat := 118140960795 + 1709816 * 2 ^ 59
def prefixEnd_1709816 : Nat := 4983230072969 + 3 ^ 40 * 1709816 * 2
def baseEnd_1709816 : Nat := 877957438747987570736705

theorem tailTrace_1709816 : CollatzResearch.WordTrace tailWord_1709816 prefixEnd_1709816 877957438747987570736705 := by
  unfold tailWord_1709816
  simp only [CollatzResearch.WordTrace]
  refine ⟨31181056386818060084770651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41574741849090746779694201 31181056386818060084770651)
  ·
    refine ⟨46771584580227090127155977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31181056386818060084770651 46771584580227090127155977)
    ·
      refine ⟨35078688435170317595366983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46771584580227090127155977 35078688435170317595366983)
      ·
        refine ⟨52618032652755476393050475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35078688435170317595366983 52618032652755476393050475)
        ·
          refine ⟨78927048979133214589575713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52618032652755476393050475 78927048979133214589575713)
          ·
            refine ⟨59195286734349910942181785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78927048979133214589575713 59195286734349910942181785)
            ·
              refine ⟨44396465050762433206636339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59195286734349910942181785 44396465050762433206636339)
              ·
                refine ⟨66594697576143649809954509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44396465050762433206636339 66594697576143649809954509)
                ·
                  refine ⟨24973011591053868678732941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66594697576143649809954509 24973011591053868678732941)
                  ·
                    refine ⟨9364879346645200754524853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24973011591053868678732941 9364879346645200754524853)
                    ·
                      refine ⟨877957438747987570736705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9364879346645200754524853 877957438747987570736705)
                      ·
                        rfl

theorem cell23_1709816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_1709816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709816 prefixEnd_1709816 := by exact prefixLift 1709816
  have htrace : WordTrace (prefixWord ++ tailWord_1709816) baseStart_1709816 baseEnd_1709816 := by
    simpa [prefixWord, tailWord_1709816, baseEnd_1709816] using wordTrace_append hprefix tailTrace_1709816
  have hstable : (prefixWord ++ tailWord_1709816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709816).length < 2 ^ (prefixWord ++ tailWord_1709816).sum := by decide
  have hdescent : baseEnd_1709816 < baseStart_1709816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709847 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_1709847 : Nat := 118140960795 + 1709847 * 2 ^ 59
def prefixEnd_1709847 : Nat := 4983230072969 + 3 ^ 40 * 1709847 * 2
def baseEnd_1709847 : Nat := 877973356648276949449063

theorem tailTrace_1709847 : CollatzResearch.WordTrace tailWord_1709847 prefixEnd_1709847 877973356648276949449063 := by
  unfold tailWord_1709847
  simp only [CollatzResearch.WordTrace]
  refine ⟨62363243436523812463919795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41575495624349208309279863 62363243436523812463919795)
  ·
    refine ⟨93544865154785718695879693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62363243436523812463919795 93544865154785718695879693)
    ·
      refine ⟨35079324433044644510954885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93544865154785718695879693 35079324433044644510954885)
      ·
        refine ⟨6577373331195870845804041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35079324433044644510954885 6577373331195870845804041)
        ·
          refine ⟨4933029998396903134353031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6577373331195870845804041 4933029998396903134353031)
          ·
            refine ⟨7399544997595354701529547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933029998396903134353031 7399544997595354701529547)
            ·
              refine ⟨11099317496393032052294321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7399544997595354701529547 11099317496393032052294321)
              ·
                refine ⟨8324488122294774039220741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11099317496393032052294321 8324488122294774039220741)
                ·
                  refine ⟨1560841522930270132353889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8324488122294774039220741 1560841522930270132353889)
                  ·
                    refine ⟨1170631142197702599265417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1560841522930270132353889 1170631142197702599265417)
                    ·
                      refine ⟨877973356648276949449063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170631142197702599265417 877973356648276949449063)
                      ·
                        rfl

theorem cell23_1709847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_1709847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709847 prefixEnd_1709847 := by exact prefixLift 1709847
  have htrace : WordTrace (prefixWord ++ tailWord_1709847) baseStart_1709847 baseEnd_1709847 := by
    simpa [prefixWord, tailWord_1709847, baseEnd_1709847] using wordTrace_append hprefix tailTrace_1709847
  have hstable : (prefixWord ++ tailWord_1709847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709847).length < 2 ^ (prefixWord ++ tailWord_1709847).sum := by decide
  have hdescent : baseEnd_1709847 < baseStart_1709847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709881 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1709881 : Nat := 118140960795 + 1709881 * 2 ^ 59
def prefixEnd_1709881 : Nat := 4983230072969 + 3 ^ 40 * 1709881 * 2
def baseEnd_1709881 : Nat := 877990814990529816423907

theorem tailTrace_1709881 : CollatzResearch.WordTrace tailWord_1709881 prefixEnd_1709881 877990814990529816423907 := by
  unfold tailWord_1709881
  simp only [CollatzResearch.WordTrace]
  refine ⟨62364483518400636270657497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41576322345600424180438331 62364483518400636270657497)
  ·
    refine ⟨46773362638800477202993123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62364483518400636270657497 46773362638800477202993123)
    ·
      refine ⟨70160043958200715804489685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46773362638800477202993123 70160043958200715804489685)
      ·
        refine ⟨1644376030270329276667727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 70160043958200715804489685 1644376030270329276667727)
        ·
          refine ⟨2466564045405493915001591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644376030270329276667727 2466564045405493915001591)
          ·
            refine ⟨3699846068108240872502387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466564045405493915001591 3699846068108240872502387)
            ·
              refine ⟨5549769102162361308753581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3699846068108240872502387 5549769102162361308753581)
              ·
                refine ⟨2081163413310885490782593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5549769102162361308753581 2081163413310885490782593)
                ·
                  refine ⟨1560872559983164118086945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081163413310885490782593 1560872559983164118086945)
                  ·
                    refine ⟨1170654419987373088565209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1560872559983164118086945 1170654419987373088565209)
                    ·
                      refine ⟨877990814990529816423907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170654419987373088565209 877990814990529816423907)
                      ·
                        rfl

theorem cell23_1709881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1709881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709881 prefixEnd_1709881 := by exact prefixLift 1709881
  have htrace : WordTrace (prefixWord ++ tailWord_1709881) baseStart_1709881 baseEnd_1709881 := by
    simpa [prefixWord, tailWord_1709881, baseEnd_1709881] using wordTrace_append hprefix tailTrace_1709881
  have hstable : (prefixWord ++ tailWord_1709881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709881).length < 2 ^ (prefixWord ++ tailWord_1709881).sum := by decide
  have hdescent : baseEnd_1709881 < baseStart_1709881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709920 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_1709920 : Nat := 118140960795 + 1709920 * 2 ^ 59
def prefixEnd_1709920 : Nat := 4983230072969 + 3 ^ 40 * 1709920 * 2
def baseEnd_1709920 : Nat := 878010840736055163836227

theorem tailTrace_1709920 : CollatzResearch.WordTrace tailWord_1709920 prefixEnd_1709920 878010840736055163836227 := by
  unfold tailWord_1709920
  simp only [CollatzResearch.WordTrace]
  refine ⟨31182952982629672965663607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41577270643506230620884809 31182952982629672965663607)
  ·
    refine ⟨46774429473944509448495411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31182952982629672965663607 46774429473944509448495411)
    ·
      refine ⟨70161644210916764172743117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46774429473944509448495411 70161644210916764172743117)
      ·
        refine ⟨26310616579093786564778669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70161644210916764172743117 26310616579093786564778669)
        ·
          refine ⟨9866481217160169961792001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26310616579093786564778669 9866481217160169961792001)
          ·
            refine ⟨7399860912870127471344001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9866481217160169961792001 7399860912870127471344001)
            ·
              refine ⟨5549895684652595603508001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7399860912870127471344001 5549895684652595603508001)
              ·
                refine ⟨4162421763489446702631001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5549895684652595603508001 4162421763489446702631001)
                ·
                  refine ⟨3121816322617085026973251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4162421763489446702631001 3121816322617085026973251)
                  ·
                    refine ⟨4682724483925627540459877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3121816322617085026973251 4682724483925627540459877)
                    ·
                      refine ⟨878010840736055163836227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4682724483925627540459877 878010840736055163836227)
                      ·
                        rfl

theorem cell23_1709920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_1709920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709920 prefixEnd_1709920 := by exact prefixLift 1709920
  have htrace : WordTrace (prefixWord ++ tailWord_1709920) baseStart_1709920 baseEnd_1709920 := by
    simpa [prefixWord, tailWord_1709920, baseEnd_1709920] using wordTrace_append hprefix tailTrace_1709920
  have hstable : (prefixWord ++ tailWord_1709920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709920).length < 2 ^ (prefixWord ++ tailWord_1709920).sum := by decide
  have hdescent : baseEnd_1709920 < baseStart_1709920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709980 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1709980 : Nat := 118140960795 + 1709980 * 2 ^ 59
def prefixEnd_1709980 : Nat := 4983230072969 + 3 ^ 40 * 1709980 * 2
def baseEnd_1709980 : Nat := 878041649575324929085951

theorem tailTrace_1709980 : CollatzResearch.WordTrace tailWord_1709980 prefixEnd_1709980 878041649575324929085951 := by
  unfold tailWord_1709980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31184047172520988089255697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41578729563361317452340929 31184047172520988089255697)
  ·
    refine ⟨23388035379390741066941773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31184047172520988089255697 23388035379390741066941773)
    ·
      refine ⟨8770513267271527900103165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23388035379390741066941773 8770513267271527900103165)
      ·
        refine ⟨3288942475226822962538687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8770513267271527900103165 3288942475226822962538687)
        ·
          refine ⟨4933413712840234443808031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3288942475226822962538687 4933413712840234443808031)
          ·
            refine ⟨7400120569260351665712047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933413712840234443808031 7400120569260351665712047)
            ·
              refine ⟨11100180853890527498568071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7400120569260351665712047 11100180853890527498568071)
              ·
                refine ⟨16650271280835791247852107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11100180853890527498568071 16650271280835791247852107)
                ·
                  refine ⟨24975406921253686871778161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16650271280835791247852107 24975406921253686871778161)
                  ·
                    refine ⟨18731555190940265153833621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24975406921253686871778161 18731555190940265153833621)
                    ·
                      refine ⟨878041649575324929085951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18731555190940265153833621 878041649575324929085951)
                      ·
                        rfl

theorem cell23_1709980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1709980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709980 prefixEnd_1709980 := by exact prefixLift 1709980
  have htrace : WordTrace (prefixWord ++ tailWord_1709980) baseStart_1709980 baseEnd_1709980 := by
    simpa [prefixWord, tailWord_1709980, baseEnd_1709980] using wordTrace_append hprefix tailTrace_1709980
  have hstable : (prefixWord ++ tailWord_1709980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709980).length < 2 ^ (prefixWord ++ tailWord_1709980).sum := by decide
  have hdescent : baseEnd_1709980 < baseStart_1709980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1709993 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_1709993 : Nat := 118140960795 + 1709993 * 2 ^ 59
def prefixEnd_1709993 : Nat := 4983230072969 + 3 ^ 40 * 1709993 * 2
def baseEnd_1709993 : Nat := 878048324823833378223391

theorem tailTrace_1709993 : CollatzResearch.WordTrace tailWord_1709993 prefixEnd_1709993 878048324823833378223391 := by
  unfold tailWord_1709993
  simp only [CollatzResearch.WordTrace]
  refine ⟨62368568493994879398734633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41579045662663252932489755 62368568493994879398734633)
  ·
    refine ⟨46776426370496159549050975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62368568493994879398734633 46776426370496159549050975)
    ·
      refine ⟨70164639555744239323576463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46776426370496159549050975 70164639555744239323576463)
      ·
        refine ⟨105246959333616358985364695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70164639555744239323576463 105246959333616358985364695)
        ·
          refine ⟨157870439000424538478047043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105246959333616358985364695 157870439000424538478047043)
          ·
            refine ⟨236805658500636807717070565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157870439000424538478047043 236805658500636807717070565)
            ·
              refine ⟨44401060968869401446950731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236805658500636807717070565 44401060968869401446950731)
              ·
                refine ⟨66601591453304102170426097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44401060968869401446950731 66601591453304102170426097)
                ·
                  refine ⟨49951193589978076627819573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66601591453304102170426097 49951193589978076627819573)
                  ·
                    refine ⟨4682924399060444683858085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49951193589978076627819573 4682924399060444683858085)
                    ·
                      refine ⟨878048324823833378223391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4682924399060444683858085 878048324823833378223391)
                      ·
                        rfl

theorem cell23_1709993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_1709993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1709993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1709993 prefixEnd_1709993 := by exact prefixLift 1709993
  have htrace : WordTrace (prefixWord ++ tailWord_1709993) baseStart_1709993 baseEnd_1709993 := by
    simpa [prefixWord, tailWord_1709993, baseEnd_1709993] using wordTrace_append hprefix tailTrace_1709993
  have hstable : (prefixWord ++ tailWord_1709993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1709993).length < 2 ^ (prefixWord ++ tailWord_1709993).sum := by decide
  have hdescent : baseEnd_1709993 < baseStart_1709993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1709993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710037 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_1710037 : Nat := 118140960795 + 1710037 * 2 ^ 59
def prefixEnd_1710037 : Nat := 4983230072969 + 3 ^ 40 * 1710037 * 2
def baseEnd_1710037 : Nat := 292690305990877068691063

theorem tailTrace_1710037 : CollatzResearch.WordTrace tailWord_1710037 prefixEnd_1710037 292690305990877068691063 := by
  unfold tailWord_1710037
  simp only [CollatzResearch.WordTrace]
  refine ⟨62370173305835474913336365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41580115537223649942224243 62370173305835474913336365)
  ·
    refine ⟨23388814989688303092501137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62370173305835474913336365 23388814989688303092501137)
    ·
      refine ⟨17541611242266227319375853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23388814989688303092501137 17541611242266227319375853)
      ·
        refine ⟨6578104215849835244765945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17541611242266227319375853 6578104215849835244765945)
        ·
          refine ⟨4933578161887376433574459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6578104215849835244765945 4933578161887376433574459)
          ·
            refine ⟨7400367242831064650361689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4933578161887376433574459 7400367242831064650361689)
            ·
              refine ⟨5550275432123298487771267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7400367242831064650361689 5550275432123298487771267)
              ·
                refine ⟨8325413148184947731656901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550275432123298487771267 8325413148184947731656901)
                ·
                  refine ⟨1561014965284677699685669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8325413148184947731656901 1561014965284677699685669)
                  ·
                    refine ⟨292690305990877068691063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561014965284677699685669 292690305990877068691063)
                    ·
                      rfl

theorem cell23_1710037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_1710037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710037 prefixEnd_1710037 := by exact prefixLift 1710037
  have htrace : WordTrace (prefixWord ++ tailWord_1710037) baseStart_1710037 baseEnd_1710037 := by
    simpa [prefixWord, tailWord_1710037, baseEnd_1710037] using wordTrace_append hprefix tailTrace_1710037
  have hstable : (prefixWord ++ tailWord_1710037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710037).length < 2 ^ (prefixWord ++ tailWord_1710037).sum := by decide
  have hdescent : baseEnd_1710037 < baseStart_1710037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710038 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_1710038 : Nat := 118140960795 + 1710038 * 2 ^ 59
def prefixEnd_1710038 : Nat := 4983230072969 + 3 ^ 40 * 1710038 * 2
def baseEnd_1710038 : Nat := 878071431453285702160685

theorem tailTrace_1710038 : CollatzResearch.WordTrace tailWord_1710038 prefixEnd_1710038 878071431453285702160685 := by
  unfold tailWord_1710038
  simp only [CollatzResearch.WordTrace]
  refine ⟨3898138111176990755257673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41580139852554568056081845 3898138111176990755257673)
  ·
    refine ⟨2923603583382743066443255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3898138111176990755257673 2923603583382743066443255)
    ·
      refine ⟨4385405375074114599664883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923603583382743066443255 4385405375074114599664883)
      ·
        refine ⟨6578108062611171899497325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385405375074114599664883 6578108062611171899497325)
        ·
          refine ⟨2466790523479189462311497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578108062611171899497325 2466790523479189462311497)
          ·
            refine ⟨1850092892609392096733623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2466790523479189462311497 1850092892609392096733623)
            ·
              refine ⟨2775139338914088145100435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850092892609392096733623 2775139338914088145100435)
              ·
                refine ⟨4162709008371132217650653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775139338914088145100435 4162709008371132217650653)
                ·
                  refine ⟨1561015878139174581618995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4162709008371132217650653 1561015878139174581618995)
                  ·
                    refine ⟨2341523817208761872428493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1561015878139174581618995 2341523817208761872428493)
                    ·
                      refine ⟨878071431453285702160685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2341523817208761872428493 878071431453285702160685)
                      ·
                        rfl

theorem cell23_1710038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_1710038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710038 prefixEnd_1710038 := by exact prefixLift 1710038
  have htrace : WordTrace (prefixWord ++ tailWord_1710038) baseStart_1710038 baseEnd_1710038 := by
    simpa [prefixWord, tailWord_1710038, baseEnd_1710038] using wordTrace_append hprefix tailTrace_1710038
  have hstable : (prefixWord ++ tailWord_1710038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710038).length < 2 ^ (prefixWord ++ tailWord_1710038).sum := by decide
  have hdescent : baseEnd_1710038 < baseStart_1710038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710060 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_1710060 : Nat := 118140960795 + 1710060 * 2 ^ 59
def prefixEnd_1710060 : Nat := 4983230072969 + 3 ^ 40 * 1710060 * 2
def baseEnd_1710060 : Nat := 878082728027684616085583

theorem tailTrace_1710060 : CollatzResearch.WordTrace tailWord_1710060 prefixEnd_1710060 878082728027684616085583 := by
  unfold tailWord_1710060
  simp only [CollatzResearch.WordTrace]
  refine ⟨31185506092376074920711817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41580674789834766560949089 31185506092376074920711817)
  ·
    refine ⟨23389129569282056190533863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31185506092376074920711817 23389129569282056190533863)
    ·
      refine ⟨35083694353923084285800795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23389129569282056190533863 35083694353923084285800795)
      ·
        refine ⟨52625541530884626428701193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35083694353923084285800795 52625541530884626428701193)
        ·
          refine ⟨39469156148163469821525895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52625541530884626428701193 39469156148163469821525895)
          ·
            refine ⟨59203734222245204732288843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39469156148163469821525895 59203734222245204732288843)
            ·
              refine ⟨88805601333367807098433265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59203734222245204732288843 88805601333367807098433265)
              ·
                refine ⟨66604201000025855323824949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88805601333367807098433265 66604201000025855323824949)
                ·
                  refine ⟨6244143843752423936608589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66604201000025855323824949 6244143843752423936608589)
                  ·
                    refine ⟨2341553941407158976228221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6244143843752423936608589 2341553941407158976228221)
                    ·
                      refine ⟨878082728027684616085583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2341553941407158976228221 878082728027684616085583)
                      ·
                        rfl

theorem cell23_1710060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_1710060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710060 prefixEnd_1710060 := by exact prefixLift 1710060
  have htrace : WordTrace (prefixWord ++ tailWord_1710060) baseStart_1710060 baseEnd_1710060 := by
    simpa [prefixWord, tailWord_1710060, baseEnd_1710060] using wordTrace_append hprefix tailTrace_1710060
  have hstable : (prefixWord ++ tailWord_1710060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710060).length < 2 ^ (prefixWord ++ tailWord_1710060).sum := by decide
  have hdescent : baseEnd_1710060 < baseStart_1710060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710077 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1710077 : Nat := 118140960795 + 1710077 * 2 ^ 59
def prefixEnd_1710077 : Nat := 4983230072969 + 3 ^ 40 * 1710077 * 2
def baseEnd_1710077 : Nat := 878091457198811049573005

theorem tailTrace_1710077 : CollatzResearch.WordTrace tailWord_1710077 prefixEnd_1710077 878091457198811049573005 := by
  unfold tailWord_1710077
  simp only [CollatzResearch.WordTrace]
  refine ⟨62371632225690561744792485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41581088150460374496528323 62371632225690561744792485)
  ·
    refine ⟨11694681042316980327148591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62371632225690561744792485 11694681042316980327148591)
    ·
      refine ⟨17542021563475470490722887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11694681042316980327148591 17542021563475470490722887)
      ·
        refine ⟨26313032345213205736084331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17542021563475470490722887 26313032345213205736084331)
        ·
          refine ⟨39469548517819808604126497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26313032345213205736084331 39469548517819808604126497)
          ·
            refine ⟨29602161388364856453094873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39469548517819808604126497 29602161388364856453094873)
            ·
              refine ⟨22201621041273642339821155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29602161388364856453094873 22201621041273642339821155)
              ·
                refine ⟨33302431561910463509731733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22201621041273642339821155 33302431561910463509731733)
                ·
                  refine ⟨1561051479464552977018675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33302431561910463509731733 1561051479464552977018675)
                  ·
                    refine ⟨2341577219196829465528013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1561051479464552977018675 2341577219196829465528013)
                    ·
                      refine ⟨878091457198811049573005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2341577219196829465528013 878091457198811049573005)
                      ·
                        rfl

theorem cell23_1710077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1710077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710077 prefixEnd_1710077 := by exact prefixLift 1710077
  have htrace : WordTrace (prefixWord ++ tailWord_1710077) baseStart_1710077 baseEnd_1710077 := by
    simpa [prefixWord, tailWord_1710077, baseEnd_1710077] using wordTrace_append hprefix tailTrace_1710077
  have hstable : (prefixWord ++ tailWord_1710077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710077).length < 2 ^ (prefixWord ++ tailWord_1710077).sum := by decide
  have hdescent : baseEnd_1710077 < baseStart_1710077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710140 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 9]
def baseStart_1710140 : Nat := 118140960795 + 1710140 * 2 ^ 59
def prefixEnd_1710140 : Nat := 4983230072969 + 3 ^ 40 * 1710140 * 2
def baseEnd_1710140 : Nat := 97569311831116033676135

theorem tailTrace_1710140 : CollatzResearch.WordTrace tailWord_1710140 prefixEnd_1710140 97569311831116033676135 := by
  unfold tailWord_1710140
  simp only [CollatzResearch.WordTrace]
  refine ⟨31186965012231161752167937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41582620016308215669557249 31186965012231161752167937)
  ·
    refine ⟨23390223759173371314125953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31186965012231161752167937 23390223759173371314125953)
    ·
      refine ⟨17542667819380028485594465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23390223759173371314125953 17542667819380028485594465)
      ·
        refine ⟨13157000864535021364195849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17542667819380028485594465 13157000864535021364195849)
        ·
          refine ⟨9867750648401266023146887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13157000864535021364195849 9867750648401266023146887)
          ·
            refine ⟨14801625972601899034720331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9867750648401266023146887 14801625972601899034720331)
            ·
              refine ⟨22202438958902848552080497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14801625972601899034720331 22202438958902848552080497)
              ·
                refine ⟨16651829219177136414060373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22202438958902848552080497 16651829219177136414060373)
                ·
                  refine ⟨97569311831116033676135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16651829219177136414060373 97569311831116033676135)
                  ·
                    rfl

theorem cell23_1710140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_1710140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710140 prefixEnd_1710140 := by exact prefixLift 1710140
  have htrace : WordTrace (prefixWord ++ tailWord_1710140) baseStart_1710140 baseEnd_1710140 := by
    simpa [prefixWord, tailWord_1710140, baseEnd_1710140] using wordTrace_append hprefix tailTrace_1710140
  have hstable : (prefixWord ++ tailWord_1710140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710140).length < 2 ^ (prefixWord ++ tailWord_1710140).sum := by decide
  have hdescent : baseEnd_1710140 < baseStart_1710140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710167 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_1710167 : Nat := 118140960795 + 1710167 * 2 ^ 59
def prefixEnd_1710167 : Nat := 4983230072969 + 3 ^ 40 * 1710167 * 2
def baseEnd_1710167 : Nat := 878137670457715697447591

theorem tailTrace_1710167 : CollatzResearch.WordTrace tailWord_1710167 prefixEnd_1710167 878137670457715697447591 := by
  unfold tailWord_1710167
  simp only [CollatzResearch.WordTrace]
  refine ⟨62374914795364507115568755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41583276530243004743712503 62374914795364507115568755)
  ·
    refine ⟨93562372193046760673353133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62374914795364507115568755 93562372193046760673353133)
    ·
      refine ⟨35085889572392535252507425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93562372193046760673353133 35085889572392535252507425)
      ·
        refine ⟨26314417179294401439380569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35085889572392535252507425 26314417179294401439380569)
        ·
          refine ⟨19735812884470801079535427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26314417179294401439380569 19735812884470801079535427)
          ·
            refine ⟨29603719326706201619303141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19735812884470801079535427 29603719326706201619303141)
            ·
              refine ⟨5550697373757412803619339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29603719326706201619303141 5550697373757412803619339)
              ·
                refine ⟨8326046060636119205429009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5550697373757412803619339 8326046060636119205429009)
                ·
                  refine ⟨6244534545477089404071757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8326046060636119205429009 6244534545477089404071757)
                  ·
                    refine ⟨2341700454553908526526909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6244534545477089404071757 2341700454553908526526909)
                    ·
                      refine ⟨878137670457715697447591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2341700454553908526526909 878137670457715697447591)
                      ·
                        rfl

theorem cell23_1710167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_1710167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710167 prefixEnd_1710167 := by exact prefixLift 1710167
  have htrace : WordTrace (prefixWord ++ tailWord_1710167) baseStart_1710167 baseEnd_1710167 := by
    simpa [prefixWord, tailWord_1710167, baseEnd_1710167] using wordTrace_append hprefix tailTrace_1710167
  have hstable : (prefixWord ++ tailWord_1710167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710167).length < 2 ^ (prefixWord ++ tailWord_1710167).sum := by decide
  have hdescent : baseEnd_1710167 < baseStart_1710167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710168 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_1710168 : Nat := 118140960795 + 1710168 * 2 ^ 59
def prefixEnd_1710168 : Nat := 4983230072969 + 3 ^ 40 * 1710168 * 2
def baseEnd_1710168 : Nat := 878138183938370193535087

theorem tailTrace_1710168 : CollatzResearch.WordTrace tailWord_1710168 prefixEnd_1710168 878138183938370193535087 := by
  unfold tailWord_1710168
  simp only [CollatzResearch.WordTrace]
  refine ⟨31187475634180442143177579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41583300845573922857570105 31187475634180442143177579)
  ·
    refine ⟨46781213451270663214766369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31187475634180442143177579 46781213451270663214766369)
    ·
      refine ⟨35085910088452997411074777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46781213451270663214766369 35085910088452997411074777)
      ·
        refine ⟨26314432566339748058306083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35085910088452997411074777 26314432566339748058306083)
        ·
          refine ⟨39471648849509622087459125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26314432566339748058306083 39471648849509622087459125)
          ·
            refine ⟨3700467079641527070699293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39471648849509622087459125 3700467079641527070699293)
            ·
              refine ⟨1387675154865572651512235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700467079641527070699293 1387675154865572651512235)
              ·
                refine ⟨2081512732298358977268353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387675154865572651512235 2081512732298358977268353)
                ·
                  refine ⟨1561134549223769232951265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2081512732298358977268353 1561134549223769232951265)
                  ·
                    refine ⟨1170850911917826924713449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1561134549223769232951265 1170850911917826924713449)
                    ·
                      refine ⟨878138183938370193535087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1170850911917826924713449 878138183938370193535087)
                      ·
                        rfl

theorem cell23_1710168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_1710168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710168 prefixEnd_1710168 := by exact prefixLift 1710168
  have htrace : WordTrace (prefixWord ++ tailWord_1710168) baseStart_1710168 baseEnd_1710168 := by
    simpa [prefixWord, tailWord_1710168, baseEnd_1710168] using wordTrace_append hprefix tailTrace_1710168
  have hstable : (prefixWord ++ tailWord_1710168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710168).length < 2 ^ (prefixWord ++ tailWord_1710168).sum := by decide
  have hdescent : baseEnd_1710168 < baseStart_1710168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710170 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_1710170 : Nat := 118140960795 + 1710170 * 2 ^ 59
def prefixEnd_1710170 : Nat := 4983230072969 + 3 ^ 40 * 1710170 * 2
def baseEnd_1710170 : Nat := 292713070299893061903359

theorem tailTrace_1710170 : CollatzResearch.WordTrace tailWord_1710170 prefixEnd_1710170 292713070299893061903359 := by
  unfold tailWord_1710170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593756053588409656981991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41583349476235759085285309 15593756053588409656981991)
  ·
    refine ⟨23390634080382614485472987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15593756053588409656981991 23390634080382614485472987)
    ·
      refine ⟨35085951120573921728209481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23390634080382614485472987 35085951120573921728209481)
      ·
        refine ⟨26314463340430441296157111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35085951120573921728209481 26314463340430441296157111)
        ·
          refine ⟨39471695010645661944235667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26314463340430441296157111 39471695010645661944235667)
          ·
            refine ⟨59207542515968492916353501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39471695010645661944235667 59207542515968492916353501)
            ·
              refine ⟨22202828443488184843632563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59207542515968492916353501 22202828443488184843632563)
              ·
                refine ⟨33304242665232277265448845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22202828443488184843632563 33304242665232277265448845)
                ·
                  refine ⟨12489090999462103974543317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33304242665232277265448845 12489090999462103974543317)
                  ·
                    refine ⟨292713070299893061903359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12489090999462103974543317 292713070299893061903359)
                    ·
                      rfl

theorem cell23_1710170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_1710170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710170 prefixEnd_1710170 := by exact prefixLift 1710170
  have htrace : WordTrace (prefixWord ++ tailWord_1710170) baseStart_1710170 baseEnd_1710170 := by
    simpa [prefixWord, tailWord_1710170, baseEnd_1710170] using wordTrace_append hprefix tailTrace_1710170
  have hstable : (prefixWord ++ tailWord_1710170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710170).length < 2 ^ (prefixWord ++ tailWord_1710170).sum := by decide
  have hdescent : baseEnd_1710170 < baseStart_1710170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710227 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3]
def baseStart_1710227 : Nat := 118140960795 + 1710227 * 2 ^ 59
def prefixEnd_1710227 : Nat := 4983230072969 + 3 ^ 40 * 1710227 * 2
def baseEnd_1710227 : Nat := 878168479296985462697315

theorem tailTrace_1710227 : CollatzResearch.WordTrace tailWord_1710227 prefixEnd_1710227 878168479296985462697315 := by
  unfold tailWord_1710227
  simp only [CollatzResearch.WordTrace]
  refine ⟨62377103175147137362752935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41584735450098091575168623 62377103175147137362752935)
  ·
    refine ⟨93565654762720706044129403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62377103175147137362752935 93565654762720706044129403)
    ·
      refine ⟨140348482144081059066194105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93565654762720706044129403 140348482144081059066194105)
      ·
        refine ⟨105261361608060794299645579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140348482144081059066194105 105261361608060794299645579)
        ·
          refine ⟨157892042412091191449468369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105261361608060794299645579 157892042412091191449468369)
          ·
            refine ⟨118419031809068393587101277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157892042412091191449468369 118419031809068393587101277)
            ·
              refine ⟨44407136928400647595162979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118419031809068393587101277 44407136928400647595162979)
              ·
                refine ⟨66610705392600971392744469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44407136928400647595162979 66610705392600971392744469)
                ·
                  refine ⟨3122376815278170534034897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 66610705392600971392744469 3122376815278170534034897)
                  ·
                    refine ⟨2341782611458627900526173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122376815278170534034897 2341782611458627900526173)
                    ·
                      refine ⟨878168479296985462697315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2341782611458627900526173 878168479296985462697315)
                      ·
                        rfl

theorem cell23_1710227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 3].length) (baseStart_1710227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710227 prefixEnd_1710227 := by exact prefixLift 1710227
  have htrace : WordTrace (prefixWord ++ tailWord_1710227) baseStart_1710227 baseEnd_1710227 := by
    simpa [prefixWord, tailWord_1710227, baseEnd_1710227] using wordTrace_append hprefix tailTrace_1710227
  have hstable : (prefixWord ++ tailWord_1710227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710227).length < 2 ^ (prefixWord ++ tailWord_1710227).sum := by decide
  have hdescent : baseEnd_1710227 < baseStart_1710227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710268 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_1710268 : Nat := 118140960795 + 1710268 * 2 ^ 59
def prefixEnd_1710268 : Nat := 4983230072969 + 3 ^ 40 * 1710268 * 2
def baseEnd_1710268 : Nat := 292729844001273267428209

theorem tailTrace_1710268 : CollatzResearch.WordTrace tailWord_1710268 prefixEnd_1710268 292729844001273267428209 := by
  unfold tailWord_1710268
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189299283999300682497729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41585732378665734243330305 31189299283999300682497729)
  ·
    refine ⟨23391974462999475511873297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31189299283999300682497729 23391974462999475511873297)
    ·
      refine ⟨17543980847249606633904973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23391974462999475511873297 17543980847249606633904973)
      ·
        refine ⟨6578992817718602487714365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17543980847249606633904973 6578992817718602487714365)
        ·
          refine ⟨2467122306644475932892887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578992817718602487714365 2467122306644475932892887)
          ·
            refine ⟨3700683459966713899339331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467122306644475932892887 3700683459966713899339331)
            ·
              refine ⟨5551025189950070849008997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700683459966713899339331 5551025189950070849008997)
              ·
                refine ⟨1040817223115638284189187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5551025189950070849008997 1040817223115638284189187)
                ·
                  refine ⟨1561225834673457426283781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1040817223115638284189187 1561225834673457426283781)
                  ·
                    refine ⟨292729844001273267428209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561225834673457426283781 292729844001273267428209)
                    ·
                      rfl

theorem cell23_1710268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_1710268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710268 prefixEnd_1710268 := by exact prefixLift 1710268
  have htrace : WordTrace (prefixWord ++ tailWord_1710268) baseStart_1710268 baseEnd_1710268 := by
    simpa [prefixWord, tailWord_1710268, baseEnd_1710268] using wordTrace_append hprefix tailTrace_1710268
  have hstable : (prefixWord ++ tailWord_1710268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710268).length < 2 ^ (prefixWord ++ tailWord_1710268).sum := by decide
  have hdescent : baseEnd_1710268 < baseStart_1710268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710277 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_1710277 : Nat := 118140960795 + 1710277 * 2 ^ 59
def prefixEnd_1710277 : Nat := 4983230072969 + 3 ^ 40 * 1710277 * 2
def baseEnd_1710277 : Nat := 292731384443236755690695

theorem tailTrace_1710277 : CollatzResearch.WordTrace tailWord_1710277 prefixEnd_1710277 292731384443236755690695 := by
  unfold tailWord_1710277
  simp only [CollatzResearch.WordTrace]
  refine ⟨62378926824965995902073085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41585951216643997268048723 62378926824965995902073085)
  ·
    refine ⟨23392097559362248463277407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62378926824965995902073085 23392097559362248463277407)
    ·
      refine ⟨35088146339043372694916111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23392097559362248463277407 35088146339043372694916111)
      ·
        refine ⟨52632219508565059042374167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35088146339043372694916111 52632219508565059042374167)
        ·
          refine ⟨78948329262847588563561251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52632219508565059042374167 78948329262847588563561251)
          ·
            refine ⟨118422493894271382845341877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78948329262847588563561251 118422493894271382845341877)
            ·
              refine ⟨11102108802587942141750801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118422493894271382845341877 11102108802587942141750801)
              ·
                refine ⟨8326581601940956606313101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11102108802587942141750801 8326581601940956606313101)
                ·
                  refine ⟨3122468100727858727367413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8326581601940956606313101 3122468100727858727367413)
                  ·
                    refine ⟨292731384443236755690695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3122468100727858727367413 292731384443236755690695)
                    ·
                      rfl

theorem cell23_1710277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_1710277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710277 prefixEnd_1710277 := by exact prefixLift 1710277
  have htrace : WordTrace (prefixWord ++ tailWord_1710277) baseStart_1710277 baseEnd_1710277 := by
    simpa [prefixWord, tailWord_1710277, baseEnd_1710277] using wordTrace_append hprefix tailTrace_1710277
  have hstable : (prefixWord ++ tailWord_1710277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710277).length < 2 ^ (prefixWord ++ tailWord_1710277).sum := by decide
  have hdescent : baseEnd_1710277 < baseStart_1710277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710311 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 1, 5]
def baseStart_1710311 : Nat := 118140960795 + 1710311 * 2 ^ 59
def prefixEnd_1710311 : Nat := 4983230072969 + 3 ^ 40 * 1710311 * 2
def baseEnd_1710311 : Nat := 292737203890654378015643

theorem tailTrace_1710311 : CollatzResearch.WordTrace tailWord_1710311 prefixEnd_1710311 292737203890654378015643 := by
  unfold tailWord_1710311
  simp only [CollatzResearch.WordTrace]
  refine ⟨62380166906842819708810787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41586777937895213139207191 62380166906842819708810787)
  ·
    refine ⟨93570250360264229563216181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62380166906842819708810787 93570250360264229563216181)
    ·
      refine ⟨8772210971274771521551517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93570250360264229563216181 8772210971274771521551517)
      ·
        refine ⟨3289579114228039320581819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8772210971274771521551517 3289579114228039320581819)
        ·
          refine ⟨4934368671342058980872729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289579114228039320581819 4934368671342058980872729)
          ·
            refine ⟨3700776503506544235654547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934368671342058980872729 3700776503506544235654547)
            ·
              refine ⟨5551164755259816353481821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700776503506544235654547 5551164755259816353481821)
              ·
                refine ⟨2081686783222431132555683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5551164755259816353481821 2081686783222431132555683)
                ·
                  refine ⟨3122530174833646698833525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081686783222431132555683 3122530174833646698833525)
                  ·
                    refine ⟨292737203890654378015643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3122530174833646698833525 292737203890654378015643)
                    ·
                      rfl

theorem cell23_1710311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_1710311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710311 prefixEnd_1710311 := by exact prefixLift 1710311
  have htrace : WordTrace (prefixWord ++ tailWord_1710311) baseStart_1710311 baseEnd_1710311 := by
    simpa [prefixWord, tailWord_1710311, baseEnd_1710311] using wordTrace_append hprefix tailTrace_1710311
  have hstable : (prefixWord ++ tailWord_1710311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710311).length < 2 ^ (prefixWord ++ tailWord_1710311).sum := by decide
  have hdescent : baseEnd_1710311 < baseStart_1710311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710337 : List Nat := [1, 2, 4, 1, 1, 2, 2, 10]
def baseStart_1710337 : Nat := 118140960795 + 1710337 * 2 ^ 59
def prefixEnd_1710337 : Nat := 4983230072969 + 3 ^ 40 * 1710337 * 2
def baseEnd_1710337 : Nat := 32526850450702964160067

theorem tailTrace_1710337 : CollatzResearch.WordTrace tailWord_1710337 prefixEnd_1710337 32526850450702964160067 := by
  unfold tailWord_1710337
  simp only [CollatzResearch.WordTrace]
  refine ⟨62381115204748626149257265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41587410136499084099504843 62381115204748626149257265)
  ·
    refine ⟨46785836403561469611942949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62381115204748626149257265 46785836403561469611942949)
    ·
      refine ⟨8772344325667775552239303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46785836403561469611942949 8772344325667775552239303)
      ·
        refine ⟨13158516488501663328358955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8772344325667775552239303 13158516488501663328358955)
        ·
          refine ⟨19737774732752494992538433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13158516488501663328358955 19737774732752494992538433)
          ·
            refine ⟨14803331049564371244403825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19737774732752494992538433 14803331049564371244403825)
            ·
              refine ⟨11102498287173278433302869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14803331049564371244403825 11102498287173278433302869)
              ·
                refine ⟨32526850450702964160067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11102498287173278433302869 32526850450702964160067)
                ·
                  rfl

theorem cell23_1710337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 10].length) (baseStart_1710337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710337 prefixEnd_1710337 := by exact prefixLift 1710337
  have htrace : WordTrace (prefixWord ++ tailWord_1710337) baseStart_1710337 baseEnd_1710337 := by
    simpa [prefixWord, tailWord_1710337, baseEnd_1710337] using wordTrace_append hprefix tailTrace_1710337
  have hstable : (prefixWord ++ tailWord_1710337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710337).length < 2 ^ (prefixWord ++ tailWord_1710337).sum := by decide
  have hdescent : baseEnd_1710337 < baseStart_1710337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710344 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_1710344 : Nat := 118140960795 + 1710344 * 2 ^ 59
def prefixEnd_1710344 : Nat := 4983230072969 + 3 ^ 40 * 1710344 * 2
def baseEnd_1710344 : Nat := 878228556533561504934277

theorem tailTrace_1710344 : CollatzResearch.WordTrace tailWord_1710344 prefixEnd_1710344 878228556533561504934277 := by
  unfold tailWord_1710344
  simp only [CollatzResearch.WordTrace]
  refine ⟨31190685257861633172381043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41587580343815510896508057 31190685257861633172381043)
  ·
    refine ⟨46786027886792449758571565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31190685257861633172381043 46786027886792449758571565)
    ·
      refine ⟨17544760457547168659464337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46786027886792449758571565 17544760457547168659464337)
      ·
        refine ⟨13158570343160376494598253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17544760457547168659464337 13158570343160376494598253)
        ·
          refine ⟨4934463878685141185474345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13158570343160376494598253 4934463878685141185474345)
          ·
            refine ⟨3700847909013855889105759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4934463878685141185474345 3700847909013855889105759)
            ·
              refine ⟨5551271863520783833658639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3700847909013855889105759 5551271863520783833658639)
              ·
                refine ⟨8326907795281175750487959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5551271863520783833658639 8326907795281175750487959)
                ·
                  refine ⟨12490361692921763625731939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8326907795281175750487959 12490361692921763625731939)
                  ·
                    refine ⟨18735542539382645438597909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12490361692921763625731939 18735542539382645438597909)
                    ·
                      refine ⟨878228556533561504934277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18735542539382645438597909 878228556533561504934277)
                      ·
                        rfl

theorem cell23_1710344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_1710344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710344 prefixEnd_1710344 := by exact prefixLift 1710344
  have htrace : WordTrace (prefixWord ++ tailWord_1710344) baseStart_1710344 baseEnd_1710344 := by
    simpa [prefixWord, tailWord_1710344, baseEnd_1710344] using wordTrace_append hprefix tailTrace_1710344
  have hstable : (prefixWord ++ tailWord_1710344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710344).length < 2 ^ (prefixWord ++ tailWord_1710344).sum := by decide
  have hdescent : baseEnd_1710344 < baseStart_1710344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710364 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1710364 : Nat := 118140960795 + 1710364 * 2 ^ 59
def prefixEnd_1710364 : Nat := 4983230072969 + 3 ^ 40 * 1710364 * 2
def baseEnd_1710364 : Nat := 878238826146651426684185

theorem tailTrace_1710364 : CollatzResearch.WordTrace tailWord_1710364 prefixEnd_1710364 878238826146651426684185 := by
  unfold tailWord_1710364
  simp only [CollatzResearch.WordTrace]
  refine ⟨31191049987825404880245073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41588066650433873173660097 31191049987825404880245073)
  ·
    refine ⟨23393287490869053660183805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31191049987825404880245073 23393287490869053660183805)
    ·
      refine ⟨8772482809075895122568927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23393287490869053660183805 8772482809075895122568927)
      ·
        refine ⟨13158724213613842683853391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8772482809075895122568927 13158724213613842683853391)
        ·
          refine ⟨19738086320420764025780087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13158724213613842683853391 19738086320420764025780087)
          ·
            refine ⟨29607129480631146038670131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19738086320420764025780087 29607129480631146038670131)
            ·
              refine ⟨44410694220946719058005197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29607129480631146038670131 44410694220946719058005197)
              ·
                refine ⟨16654010332855019646751949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44410694220946719058005197 16654010332855019646751949)
                ·
                  refine ⟨6245253874820632367531981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16654010332855019646751949 6245253874820632367531981)
                  ·
                    refine ⟨2341970203057737137824493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6245253874820632367531981 2341970203057737137824493)
                    ·
                      refine ⟨878238826146651426684185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2341970203057737137824493 878238826146651426684185)
                      ·
                        rfl

theorem cell23_1710364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1710364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710364 prefixEnd_1710364 := by exact prefixLift 1710364
  have htrace : WordTrace (prefixWord ++ tailWord_1710364) baseStart_1710364 baseEnd_1710364 := by
    simpa [prefixWord, tailWord_1710364, baseEnd_1710364] using wordTrace_append hprefix tailTrace_1710364
  have hstable : (prefixWord ++ tailWord_1710364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710364).length < 2 ^ (prefixWord ++ tailWord_1710364).sum := by decide
  have hdescent : baseEnd_1710364 < baseStart_1710364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710408 : List Nat := [2, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_1710408 : Nat := 118140960795 + 1710408 * 2 ^ 59
def prefixEnd_1710408 : Nat := 4983230072969 + 3 ^ 40 * 1710408 * 2
def baseEnd_1710408 : Nat := 878261419295449254533983

theorem tailTrace_1710408 : CollatzResearch.WordTrace tailWord_1710408 prefixEnd_1710408 878261419295449254533983 := by
  unfold tailWord_1710408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31191852393745702637545939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41589136524994270183394585 31191852393745702637545939)
  ·
    refine ⟨46787778590618553956318909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31191852393745702637545939 46787778590618553956318909)
    ·
      refine ⟨17545416971481957733619591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46787778590618553956318909 17545416971481957733619591)
      ·
        refine ⟨26318125457222936600429387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17545416971481957733619591 26318125457222936600429387)
        ·
          refine ⟨39477188185834404900644081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26318125457222936600429387 39477188185834404900644081)
          ·
            refine ⟨29607891139375803675483061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39477188185834404900644081 29607891139375803675483061)
            ·
              refine ⟨2775739794316481594576537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29607891139375803675483061 2775739794316481594576537)
              ·
                refine ⟨2081804845737361195932403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775739794316481594576537 2081804845737361195932403)
                ·
                  refine ⟨3122707268606041793898605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2081804845737361195932403 3122707268606041793898605)
                  ·
                    refine ⟨1171015225727265672711977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3122707268606041793898605 1171015225727265672711977)
                    ·
                      refine ⟨878261419295449254533983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171015225727265672711977 878261419295449254533983)
                      ·
                        rfl

theorem cell23_1710408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_1710408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710408 prefixEnd_1710408 := by exact prefixLift 1710408
  have htrace : WordTrace (prefixWord ++ tailWord_1710408) baseStart_1710408 baseEnd_1710408 := by
    simpa [prefixWord, tailWord_1710408, baseEnd_1710408] using wordTrace_append hprefix tailTrace_1710408
  have hstable : (prefixWord ++ tailWord_1710408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710408).length < 2 ^ (prefixWord ++ tailWord_1710408).sum := by decide
  have hdescent : baseEnd_1710408 < baseStart_1710408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710478 : List Nat := [4, 1, 1, 4, 1, 1, 1, 5, 5]
def baseStart_1710478 : Nat := 118140960795 + 1710478 * 2 ^ 59
def prefixEnd_1710478 : Nat := 4983230072969 + 3 ^ 40 * 1710478 * 2
def baseEnd_1710478 : Nat := 97588595882362664517629

theorem tailTrace_1710478 : CollatzResearch.WordTrace tailWord_1710478 prefixEnd_1710478 97588595882362664517629 := by
  unfold tailWord_1710478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7798282237154725903767511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41590838598158538153426725 7798282237154725903767511)
  ·
    refine ⟨11697423355732088855651267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7798282237154725903767511 11697423355732088855651267)
    ·
      refine ⟨17546135033598133283476901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11697423355732088855651267 17546135033598133283476901)
      ·
        refine ⟨3289900318799649990651919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17546135033598133283476901 3289900318799649990651919)
        ·
          refine ⟨4934850478199474985977879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3289900318799649990651919 4934850478199474985977879)
          ·
            refine ⟨7402275717299212478966819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934850478199474985977879 7402275717299212478966819)
            ·
              refine ⟨11103413575948818718450229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402275717299212478966819 11103413575948818718450229)
              ·
                refine ⟨1040945022745201754854709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11103413575948818718450229 1040945022745201754854709)
                ·
                  refine ⟨97588595882362664517629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040945022745201754854709 97588595882362664517629)
                  ·
                    rfl

theorem cell23_1710478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_1710478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710478 prefixEnd_1710478 := by exact prefixLift 1710478
  have htrace : WordTrace (prefixWord ++ tailWord_1710478) baseStart_1710478 baseEnd_1710478 := by
    simpa [prefixWord, tailWord_1710478, baseEnd_1710478] using wordTrace_append hprefix tailTrace_1710478
  have hstable : (prefixWord ++ tailWord_1710478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710478).length < 2 ^ (prefixWord ++ tailWord_1710478).sum := by decide
  have hdescent : baseEnd_1710478 < baseStart_1710478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710506 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1710506 : Nat := 118140960795 + 1710506 * 2 ^ 59
def prefixEnd_1710506 : Nat := 4983230072969 + 3 ^ 40 * 1710506 * 2
def baseEnd_1710506 : Nat := 878311740399589871108533

theorem tailTrace_1710506 : CollatzResearch.WordTrace tailWord_1710506 prefixEnd_1710506 878311740399589871108533 := by
  unfold tailWord_1710506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15596819785284092003039843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41591519427424245341439581 15596819785284092003039843)
  ·
    refine ⟨23395229677926138004559765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15596819785284092003039843 23395229677926138004559765)
    ·
      refine ⟨1096651391152787718963739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23395229677926138004559765 1096651391152787718963739)
      ·
        refine ⟨1644977086729181578445609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096651391152787718963739 1644977086729181578445609)
        ·
          refine ⟨1233732815046886183834207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644977086729181578445609 1233732815046886183834207)
          ·
            refine ⟨1850599222570329275751311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233732815046886183834207 1850599222570329275751311)
            ·
              refine ⟨2775898833855493913626967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850599222570329275751311 2775898833855493913626967)
              ·
                refine ⟨4163848250783240870440451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775898833855493913626967 4163848250783240870440451)
                ·
                  refine ⟨6245772376174861305660677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4163848250783240870440451 6245772376174861305660677)
                  ·
                    refine ⟨1171082320532786494811377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6245772376174861305660677 1171082320532786494811377)
                    ·
                      refine ⟨878311740399589871108533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171082320532786494811377 878311740399589871108533)
                      ·
                        rfl

theorem cell23_1710506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1710506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710506 prefixEnd_1710506 := by exact prefixLift 1710506
  have htrace : WordTrace (prefixWord ++ tailWord_1710506) baseStart_1710506 baseEnd_1710506 := by
    simpa [prefixWord, tailWord_1710506, baseEnd_1710506] using wordTrace_append hprefix tailTrace_1710506
  have hstable : (prefixWord ++ tailWord_1710506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710506).length < 2 ^ (prefixWord ++ tailWord_1710506).sum := by decide
  have hdescent : baseEnd_1710506 < baseStart_1710506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710529 : List Nat := [1, 2, 7, 1, 1, 2, 1, 3, 5]
def baseStart_1710529 : Nat := 118140960795 + 1710529 * 2 ^ 59
def prefixEnd_1710529 : Nat := 4983230072969 + 3 ^ 40 * 1710529 * 2
def baseEnd_1710529 : Nat := 97591505606071475680103

theorem tailTrace_1710529 : CollatzResearch.WordTrace tailWord_1710529 prefixEnd_1710529 97591505606071475680103 := by
  unfold tailWord_1710529
  simp only [CollatzResearch.WordTrace]
  refine ⟨62388118020053042940246641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41592078680035361960164427 62388118020053042940246641)
  ·
    refine ⟨46791088515039782205184981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62388118020053042940246641 46791088515039782205184981)
    ·
      refine ⟨1096666137071244895434023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46791088515039782205184981 1096666137071244895434023)
      ·
        refine ⟨1644999205606867343151035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096666137071244895434023 1644999205606867343151035)
        ·
          refine ⟨2467498808410301014726553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644999205606867343151035 2467498808410301014726553)
          ·
            refine ⟨1850624106307725761044915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467498808410301014726553 1850624106307725761044915)
            ·
              refine ⟨2775936159461588641567373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850624106307725761044915 2775936159461588641567373)
              ·
                refine ⟨1040976059798095740587765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2775936159461588641567373 1040976059798095740587765)
                ·
                  refine ⟨97591505606071475680103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1040976059798095740587765 97591505606071475680103)
                  ·
                    rfl

theorem cell23_1710529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 3, 5].length) (baseStart_1710529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710529 prefixEnd_1710529 := by exact prefixLift 1710529
  have htrace : WordTrace (prefixWord ++ tailWord_1710529) baseStart_1710529 baseEnd_1710529 := by
    simpa [prefixWord, tailWord_1710529, baseEnd_1710529] using wordTrace_append hprefix tailTrace_1710529
  have hstable : (prefixWord ++ tailWord_1710529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710529).length < 2 ^ (prefixWord ++ tailWord_1710529).sum := by decide
  have hdescent : baseEnd_1710529 < baseStart_1710529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710531 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1710531 : Nat := 118140960795 + 1710531 * 2 ^ 59
def prefixEnd_1710531 : Nat := 4983230072969 + 3 ^ 40 * 1710531 * 2
def baseEnd_1710531 : Nat := 878324577415952273295917

theorem tailTrace_1710531 : CollatzResearch.WordTrace tailWord_1710531 prefixEnd_1710531 878324577415952273295917 := by
  unfold tailWord_1710531
  simp only [CollatzResearch.WordTrace]
  refine ⟨62388190966045797281819447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41592127310697198187879631 62388190966045797281819447)
  ·
    refine ⟨93582286449068695922729171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62388190966045797281819447 93582286449068695922729171)
    ·
      refine ⟨140373429673603043884093757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93582286449068695922729171 140373429673603043884093757)
      ·
        refine ⟨52640036127601141456535159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140373429673603043884093757 52640036127601141456535159)
        ·
          refine ⟨78960054191401712184802739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52640036127601141456535159 78960054191401712184802739)
          ·
            refine ⟨118440081287102568277204109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78960054191401712184802739 118440081287102568277204109)
            ·
              refine ⟨44415030482663463103951541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118440081287102568277204109 44415030482663463103951541)
              ·
                refine ⟨4163909107749699665995457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44415030482663463103951541 4163909107749699665995457)
                ·
                  refine ⟨3122931830812274749496593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4163909107749699665995457 3122931830812274749496593)
                  ·
                    refine ⟨2342198873109206062122445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122931830812274749496593 2342198873109206062122445)
                    ·
                      refine ⟨878324577415952273295917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2342198873109206062122445 878324577415952273295917)
                      ·
                        rfl

theorem cell23_1710531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1710531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710531 prefixEnd_1710531 := by exact prefixLift 1710531
  have htrace : WordTrace (prefixWord ++ tailWord_1710531) baseStart_1710531 baseEnd_1710531 := by
    simpa [prefixWord, tailWord_1710531, baseEnd_1710531] using wordTrace_append hprefix tailTrace_1710531
  have hstable : (prefixWord ++ tailWord_1710531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710531).length < 2 ^ (prefixWord ++ tailWord_1710531).sum := by decide
  have hdescent : baseEnd_1710531 < baseStart_1710531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710548 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1710548 : Nat := 118140960795 + 1710548 * 2 ^ 59
def prefixEnd_1710548 : Nat := 4983230072969 + 3 ^ 40 * 1710548 * 2
def baseEnd_1710548 : Nat := 878333306587078706783339

theorem tailTrace_1710548 : CollatzResearch.WordTrace tailWord_1710548 prefixEnd_1710548 878333306587078706783339 := by
  unfold tailWord_1710548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31194405503492104592594149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41592540671322806123458865 31194405503492104592594149)
  ·
    refine ⟨5848951031904769611111403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31194405503492104592594149 5848951031904769611111403)
    ·
      refine ⟨8773426547857154416667105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5848951031904769611111403 8773426547857154416667105)
      ·
        refine ⟨6580069910892865812500329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8773426547857154416667105 6580069910892865812500329)
        ·
          refine ⟨4935052433169649359375247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6580069910892865812500329 4935052433169649359375247)
          ·
            refine ⟨7402578649754474039062871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935052433169649359375247 7402578649754474039062871)
            ·
              refine ⟨11103867974631711058594307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7402578649754474039062871 11103867974631711058594307)
              ·
                refine ⟨16655801961947566587891461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11103867974631711058594307 16655801961947566587891461)
                ·
                  refine ⟨3122962867865168735229649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16655801961947566587891461 3122962867865168735229649)
                  ·
                    refine ⟨2342222150898876551422237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3122962867865168735229649 2342222150898876551422237)
                    ·
                      refine ⟨878333306587078706783339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2342222150898876551422237 878333306587078706783339)
                      ·
                        rfl

theorem cell23_1710548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1710548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710548 prefixEnd_1710548 := by exact prefixLift 1710548
  have htrace : WordTrace (prefixWord ++ tailWord_1710548) baseStart_1710548 baseEnd_1710548 := by
    simpa [prefixWord, tailWord_1710548, baseEnd_1710548] using wordTrace_append hprefix tailTrace_1710548
  have hstable : (prefixWord ++ tailWord_1710548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710548).length < 2 ^ (prefixWord ++ tailWord_1710548).sum := by decide
  have hdescent : baseEnd_1710548 < baseStart_1710548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710564 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_1710564 : Nat := 118140960795 + 1710564 * 2 ^ 59
def prefixEnd_1710564 : Nat := 4983230072969 + 3 ^ 40 * 1710564 * 2
def baseEnd_1710564 : Nat := 292780507425850214727755

theorem tailTrace_1710564 : CollatzResearch.WordTrace tailWord_1710564 prefixEnd_1710564 292780507425850214727755 := by
  unfold tailWord_1710564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31194697287463121958885373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41592929716617495945180497 31194697287463121958885373)
  ·
    refine ⟨11698011482798670734582015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31194697287463121958885373 11698011482798670734582015)
    ·
      refine ⟨17547017224198006101873023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11698011482798670734582015 17547017224198006101873023)
      ·
        refine ⟨26320525836297009152809535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17547017224198006101873023 26320525836297009152809535)
        ·
          refine ⟨39480788754445513729214303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26320525836297009152809535 39480788754445513729214303)
          ·
            refine ⟨59221183131668270593821455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39480788754445513729214303 59221183131668270593821455)
            ·
              refine ⟨88831774697502405890732183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59221183131668270593821455 88831774697502405890732183)
              ·
                refine ⟨133247662046253608836098275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88831774697502405890732183 133247662046253608836098275)
                ·
                  refine ⟨199871493069380413254147413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133247662046253608836098275 199871493069380413254147413)
                  ·
                    refine ⟨292780507425850214727755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 199871493069380413254147413 292780507425850214727755)
                    ·
                      rfl

theorem cell23_1710564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_1710564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710564 prefixEnd_1710564 := by exact prefixLift 1710564
  have htrace : WordTrace (prefixWord ++ tailWord_1710564) baseStart_1710564 baseEnd_1710564 := by
    simpa [prefixWord, tailWord_1710564, baseEnd_1710564] using wordTrace_append hprefix tailTrace_1710564
  have hstable : (prefixWord ++ tailWord_1710564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710564).length < 2 ^ (prefixWord ++ tailWord_1710564).sum := by decide
  have hdescent : baseEnd_1710564 < baseStart_1710564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710568 : List Nat := [2, 1, 4, 1, 1, 3, 4, 1, 6]
def baseStart_1710568 : Nat := 118140960795 + 1710568 * 2 ^ 59
def prefixEnd_1710568 : Nat := 4983230072969 + 3 ^ 40 * 1710568 * 2
def baseEnd_1710568 : Nat := 97593730688907625392583

theorem tailTrace_1710568 : CollatzResearch.WordTrace tailWord_1710568 prefixEnd_1710568 97593730688907625392583 := by
  unfold tailWord_1710568
  simp only [CollatzResearch.WordTrace]
  refine ⟨31194770233455876300458179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41593026977941168400610905 31194770233455876300458179)
  ·
    refine ⟨46792155350183814450687269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31194770233455876300458179 46792155350183814450687269)
    ·
      refine ⟨8773529128159465209503863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46792155350183814450687269 8773529128159465209503863)
      ·
        refine ⟨13160293692239197814255795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8773529128159465209503863 13160293692239197814255795)
        ·
          refine ⟨19740440538358796721383693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13160293692239197814255795 19740440538358796721383693)
          ·
            refine ⟨7402665201884548770518885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19740440538358796721383693 7402665201884548770518885)
            ·
              refine ⟨1387999725353352894472291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7402665201884548770518885 1387999725353352894472291)
              ·
                refine ⟨2081999588030029341708437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387999725353352894472291 2081999588030029341708437)
                ·
                  refine ⟨97593730688907625392583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2081999588030029341708437 97593730688907625392583)
                  ·
                    rfl

theorem cell23_1710568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 1, 6].length) (baseStart_1710568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710568 prefixEnd_1710568 := by exact prefixLift 1710568
  have htrace : WordTrace (prefixWord ++ tailWord_1710568) baseStart_1710568 baseEnd_1710568 := by
    simpa [prefixWord, tailWord_1710568, baseEnd_1710568] using wordTrace_append hprefix tailTrace_1710568
  have hstable : (prefixWord ++ tailWord_1710568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710568).length < 2 ^ (prefixWord ++ tailWord_1710568).sum := by decide
  have hdescent : baseEnd_1710568 < baseStart_1710568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710595 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 1, 1, 3]
def baseStart_1710595 : Nat := 118140960795 + 1710595 * 2 ^ 59
def prefixEnd_1710595 : Nat := 4983230072969 + 3 ^ 40 * 1710595 * 2
def baseEnd_1710595 : Nat := 878357440177840022895623

theorem tailTrace_1710595 : CollatzResearch.WordTrace tailWord_1710595 prefixEnd_1710595 878357440177840022895623 := by
  unfold tailWord_1710595
  simp only [CollatzResearch.WordTrace]
  refine ⟨62390525237813936212149239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41593683491875957474766159 62390525237813936212149239)
  ·
    refine ⟨93585787856720904318223859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62390525237813936212149239 93585787856720904318223859)
    ·
      refine ⟨140378681785081356477335789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93585787856720904318223859 140378681785081356477335789)
      ·
        refine ⟨52642005669405508679000921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140378681785081356477335789 52642005669405508679000921)
        ·
          refine ⟨39481504252054131509250691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52642005669405508679000921 39481504252054131509250691)
          ·
            refine ⟨59222256378081197263876037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39481504252054131509250691 59222256378081197263876037)
            ·
              refine ⟨11104173070890224486976757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59222256378081197263876037 11104173070890224486976757)
              ·
                refine ⟨1041016225395958545654071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11104173070890224486976757 1041016225395958545654071)
                ·
                  refine ⟨1561524338093937818481107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041016225395958545654071 1561524338093937818481107)
                  ·
                    refine ⟨2342286507140906727721661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1561524338093937818481107 2342286507140906727721661)
                    ·
                      refine ⟨878357440177840022895623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2342286507140906727721661 878357440177840022895623)
                      ·
                        rfl

theorem cell23_1710595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_1710595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710595 prefixEnd_1710595 := by exact prefixLift 1710595
  have htrace : WordTrace (prefixWord ++ tailWord_1710595) baseStart_1710595 baseEnd_1710595 := by
    simpa [prefixWord, tailWord_1710595, baseEnd_1710595] using wordTrace_append hprefix tailTrace_1710595
  have hstable : (prefixWord ++ tailWord_1710595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710595).length < 2 ^ (prefixWord ++ tailWord_1710595).sum := by decide
  have hdescent : baseEnd_1710595 < baseStart_1710595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710651 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3]
def baseStart_1710651 : Nat := 118140960795 + 1710651 * 2 ^ 59
def prefixEnd_1710651 : Nat := 4983230072969 + 3 ^ 40 * 1710651 * 2
def baseEnd_1710651 : Nat := 878386195094491803795365

theorem tailTrace_1710651 : CollatzResearch.WordTrace tailWord_1710651 prefixEnd_1710651 878386195094491803795365 := by
  unfold tailWord_1710651
  simp only [CollatzResearch.WordTrace]
  refine ⟨62392567725611057776187807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41595045150407371850791871 62392567725611057776187807)
  ·
    refine ⟨93588851588416586664281711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62392567725611057776187807 93588851588416586664281711)
    ·
      refine ⟨140383277382624879996422567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93588851588416586664281711 140383277382624879996422567)
      ·
        refine ⟨210574916073937319994633851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140383277382624879996422567 210574916073937319994633851)
        ·
          refine ⟨315862374110905979991950777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210574916073937319994633851 315862374110905979991950777)
          ·
            refine ⟨236896780583179484993963083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315862374110905979991950777 236896780583179484993963083)
            ·
              refine ⟨355345170874769227490944625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236896780583179484993963083 355345170874769227490944625)
              ·
                refine ⟨266508878156076920618208469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 355345170874769227490944625 266508878156076920618208469)
                ·
                  refine ⟨6246301831783052826989261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266508878156076920618208469 6246301831783052826989261)
                  ·
                    refine ⟨2342363186918644810120973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6246301831783052826989261 2342363186918644810120973)
                    ·
                      refine ⟨878386195094491803795365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2342363186918644810120973 878386195094491803795365)
                      ·
                        rfl

theorem cell23_1710651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 3, 3].length) (baseStart_1710651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710651 prefixEnd_1710651 := by exact prefixLift 1710651
  have htrace : WordTrace (prefixWord ++ tailWord_1710651) baseStart_1710651 baseEnd_1710651 := by
    simpa [prefixWord, tailWord_1710651, baseEnd_1710651] using wordTrace_append hprefix tailTrace_1710651
  have hstable : (prefixWord ++ tailWord_1710651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710651).length < 2 ^ (prefixWord ++ tailWord_1710651).sum := by decide
  have hdescent : baseEnd_1710651 < baseStart_1710651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710652 : List Nat := [2, 2, 2, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_1710652 : Nat := 118140960795 + 1710652 * 2 ^ 59
def prefixEnd_1710652 : Nat := 4983230072969 + 3 ^ 40 * 1710652 * 2
def baseEnd_1710652 : Nat := 878386708575146299882861

theorem tailTrace_1710652 : CollatzResearch.WordTrace tailWord_1710652 prefixEnd_1710652 878386708575146299882861 := by
  unfold tailWord_1710652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31196302099303717473487105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41595069465738289964649473 31196302099303717473487105)
  ·
    refine ⟨23397226574477788105115329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31196302099303717473487105 23397226574477788105115329)
    ·
      refine ⟨17547919930858341078836497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23397226574477788105115329 17547919930858341078836497)
      ·
        refine ⟨13160939948143755809127373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17547919930858341078836497 13160939948143755809127373)
        ·
          refine ⟨4935352480553908428422765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13160939948143755809127373 4935352480553908428422765)
          ·
            refine ⟨1850757180207715660658537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4935352480553908428422765 1850757180207715660658537)
            ·
              refine ⟨1388067885155786745493903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1850757180207715660658537 1388067885155786745493903)
              ·
                refine ⟨2082101827733680118240855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388067885155786745493903 2082101827733680118240855)
                ·
                  refine ⟨3123152741600520177361283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082101827733680118240855 3123152741600520177361283)
                  ·
                    refine ⟨4684729112400780266041925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123152741600520177361283 4684729112400780266041925)
                    ·
                      refine ⟨878386708575146299882861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4684729112400780266041925 878386708575146299882861)
                      ·
                        rfl

theorem cell23_1710652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_1710652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710652 prefixEnd_1710652 := by exact prefixLift 1710652
  have htrace : WordTrace (prefixWord ++ tailWord_1710652) baseStart_1710652 baseEnd_1710652 := by
    simpa [prefixWord, tailWord_1710652, baseEnd_1710652] using wordTrace_append hprefix tailTrace_1710652
  have hstable : (prefixWord ++ tailWord_1710652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710652).length < 2 ^ (prefixWord ++ tailWord_1710652).sum := by decide
  have hdescent : baseEnd_1710652 < baseStart_1710652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710662 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1710662 : Nat := 118140960795 + 1710662 * 2 ^ 59
def prefixEnd_1710662 : Nat := 4983230072969 + 3 ^ 40 * 1710662 * 2
def baseEnd_1710662 : Nat := 292797281127230420252605

theorem tailTrace_1710662 : CollatzResearch.WordTrace tailWord_1710662 prefixEnd_1710662 292797281127230420252605 := by
  unfold tailWord_1710662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949780279017850207963695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41595312619047471103225493 1949780279017850207963695)
  ·
    refine ⟨2924670418526775311945543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949780279017850207963695 2924670418526775311945543)
    ·
      refine ⟨4387005627790162967918315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924670418526775311945543 4387005627790162967918315)
      ·
        refine ⟨6580508441685244451877473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4387005627790162967918315 6580508441685244451877473)
        ·
          refine ⟨4935381331263933338908105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6580508441685244451877473 4935381331263933338908105)
          ·
            refine ⟨3701535998447950004181079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935381331263933338908105 3701535998447950004181079)
            ·
              refine ⟨5552303997671925006271619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701535998447950004181079 5552303997671925006271619)
              ·
                refine ⟨8328455996507887509407429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5552303997671925006271619 8328455996507887509407429)
                ·
                  refine ⟨1561585499345228908013893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8328455996507887509407429 1561585499345228908013893)
                  ·
                    refine ⟨292797281127230420252605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561585499345228908013893 292797281127230420252605)
                    ·
                      rfl

theorem cell23_1710662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1710662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710662 prefixEnd_1710662 := by exact prefixLift 1710662
  have htrace : WordTrace (prefixWord ++ tailWord_1710662) baseStart_1710662 baseEnd_1710662 := by
    simpa [prefixWord, tailWord_1710662, baseEnd_1710662] using wordTrace_append hprefix tailTrace_1710662
  have hstable : (prefixWord ++ tailWord_1710662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710662).length < 2 ^ (prefixWord ++ tailWord_1710662).sum := by decide
  have hdescent : baseEnd_1710662 < baseStart_1710662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710669 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_1710669 : Nat := 118140960795 + 1710669 * 2 ^ 59
def prefixEnd_1710669 : Nat := 4983230072969 + 3 ^ 40 * 1710669 * 2
def baseEnd_1710669 : Nat := 878395437746272733370283

theorem tailTrace_1710669 : CollatzResearch.WordTrace tailWord_1710669 prefixEnd_1710669 878395437746272733370283 := by
  unfold tailWord_1710669
  simp only [CollatzResearch.WordTrace]
  refine ⟨62393224239545846850343061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41595482826363897900228707 62393224239545846850343061)
  ·
    refine ⟨2924682386228711571109831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62393224239545846850343061 2924682386228711571109831)
    ·
      refine ⟨4387023579343067356664747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924682386228711571109831 4387023579343067356664747)
      ·
        refine ⟨6580535369014601034997121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4387023579343067356664747 6580535369014601034997121)
        ·
          refine ⟨4935401526760950776247841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6580535369014601034997121 4935401526760950776247841)
          ·
            refine ⟨3701551145070713082185881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935401526760950776247841 3701551145070713082185881)
            ·
              refine ⟨2776163358803034811639411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701551145070713082185881 2776163358803034811639411)
              ·
                refine ⟨4164245038204552217459117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776163358803034811639411 4164245038204552217459117)
                ·
                  refine ⟨1561591889326707081547169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4164245038204552217459117 1561591889326707081547169)
                  ·
                    refine ⟨1171193916995030311160377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1561591889326707081547169 1171193916995030311160377)
                    ·
                      refine ⟨878395437746272733370283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171193916995030311160377 878395437746272733370283)
                      ·
                        rfl

theorem cell23_1710669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_1710669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710669 prefixEnd_1710669 := by exact prefixLift 1710669
  have htrace : WordTrace (prefixWord ++ tailWord_1710669) baseStart_1710669 baseEnd_1710669 := by
    simpa [prefixWord, tailWord_1710669, baseEnd_1710669] using wordTrace_append hprefix tailTrace_1710669
  have hstable : (prefixWord ++ tailWord_1710669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710669).length < 2 ^ (prefixWord ++ tailWord_1710669).sum := by decide
  have hdescent : baseEnd_1710669 < baseStart_1710669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710686 : List Nat := [4, 4, 1, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1710686 : Nat := 118140960795 + 1710686 * 2 ^ 59
def prefixEnd_1710686 : Nat := 4983230072969 + 3 ^ 40 * 1710686 * 2
def baseEnd_1710686 : Nat := 878404166917399166857705

theorem tailTrace_1710686 : CollatzResearch.WordTrace tailWord_1710686 prefixEnd_1710686 878404166917399166857705 := by
  unfold tailWord_1710686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799230535060532344213989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41595896186989505835807941 7799230535060532344213989)
  ·
    refine ⟨1462355725323849814540123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7799230535060532344213989 1462355725323849814540123)
    ·
      refine ⟨2193533587985774721810185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462355725323849814540123 2193533587985774721810185)
      ·
        refine ⟨1645150190989331041357639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2193533587985774721810185 1645150190989331041357639)
        ·
          refine ⟨2467725286483996562036459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645150190989331041357639 2467725286483996562036459)
          ·
            refine ⟨3701587929725994843054689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467725286483996562036459 3701587929725994843054689)
            ·
              refine ⟨2776190947294496132291017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3701587929725994843054689 2776190947294496132291017)
              ·
                refine ⟨2082143210470872099218263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776190947294496132291017 2082143210470872099218263)
                ·
                  refine ⟨3123214815706308148827395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082143210470872099218263 3123214815706308148827395)
                  ·
                    refine ⟨4684822223559462223241093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123214815706308148827395 4684822223559462223241093)
                    ·
                      refine ⟨878404166917399166857705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4684822223559462223241093 878404166917399166857705)
                      ·
                        rfl

theorem cell23_1710686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1710686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710686 prefixEnd_1710686 := by exact prefixLift 1710686
  have htrace : WordTrace (prefixWord ++ tailWord_1710686) baseStart_1710686 baseEnd_1710686 := by
    simpa [prefixWord, tailWord_1710686, baseEnd_1710686] using wordTrace_append hprefix tailTrace_1710686
  have hstable : (prefixWord ++ tailWord_1710686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710686).length < 2 ^ (prefixWord ++ tailWord_1710686).sum := by decide
  have hdescent : baseEnd_1710686 < baseStart_1710686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710711 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_1710711 : Nat := 118140960795 + 1710711 * 2 ^ 59
def prefixEnd_1710711 : Nat := 4983230072969 + 3 ^ 40 * 1710711 * 2
def baseEnd_1710711 : Nat := 878417003933761569045089

theorem tailTrace_1710711 : CollatzResearch.WordTrace tailWord_1710711 prefixEnd_1710711 878417003933761569045089 := by
  unfold tailWord_1710711
  simp only [CollatzResearch.WordTrace]
  refine ⟨62394756105393688023371987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41596504070262458682247991 62394756105393688023371987)
  ·
    refine ⟨93592134158090532035057981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62394756105393688023371987 93592134158090532035057981)
    ·
      refine ⟨35097050309283949513146743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93592134158090532035057981 35097050309283949513146743)
      ·
        refine ⟨52645575463925924269720115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35097050309283949513146743 52645575463925924269720115)
        ·
          refine ⟨78968363195888886404580173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52645575463925924269720115 78968363195888886404580173)
          ·
            refine ⟨29613136198458332401717565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78968363195888886404580173 29613136198458332401717565)
            ·
              refine ⟨11104926074421874650644087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29613136198458332401717565 11104926074421874650644087)
              ·
                refine ⟨16657389111632811975966131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11104926074421874650644087 16657389111632811975966131)
                ·
                  refine ⟨24986083667449217963949197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16657389111632811975966131 24986083667449217963949197)
                  ·
                    refine ⟨9369781375293456736480949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24986083667449217963949197 9369781375293456736480949)
                    ·
                      refine ⟨878417003933761569045089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9369781375293456736480949 878417003933761569045089)
                      ·
                        rfl

theorem cell23_1710711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_1710711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710711 prefixEnd_1710711 := by exact prefixLift 1710711
  have htrace : WordTrace (prefixWord ++ tailWord_1710711) baseStart_1710711 baseEnd_1710711 := by
    simpa [prefixWord, tailWord_1710711, baseEnd_1710711] using wordTrace_append hprefix tailTrace_1710711
  have hstable : (prefixWord ++ tailWord_1710711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710711).length < 2 ^ (prefixWord ++ tailWord_1710711).sum := by decide
  have hdescent : baseEnd_1710711 < baseStart_1710711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710731 : List Nat := [1, 1, 1, 1, 4, 1, 2, 5, 7]
def baseStart_1710731 : Nat := 118140960795 + 1710731 * 2 ^ 59
def prefixEnd_1710731 : Nat := 4983230072969 + 3 ^ 40 * 1710731 * 2
def baseEnd_1710731 : Nat := 97603030394094610088333

theorem tailTrace_1710731 : CollatzResearch.WordTrace tailWord_1710731 prefixEnd_1710731 97603030394094610088333 := by
  unfold tailWord_1710731
  simp only [CollatzResearch.WordTrace]
  refine ⟨62395485565321231439100047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41596990376880820959400031 62395485565321231439100047)
  ·
    refine ⟨93593228347981847158650071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62395485565321231439100047 93593228347981847158650071)
    ·
      refine ⟨140389842521972770737975107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93593228347981847158650071 140389842521972770737975107)
      ·
        refine ⟨210584763782959156106962661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140389842521972770737975107 210584763782959156106962661)
        ·
          refine ⟨39484643209304841770055499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210584763782959156106962661 39484643209304841770055499)
          ·
            refine ⟨59226964813957262655083249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39484643209304841770055499 59226964813957262655083249)
            ·
              refine ⟨44420223610467946991312437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59226964813957262655083249 44420223610467946991312437)
              ·
                refine ⟨4164395963481370030435541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44420223610467946991312437 4164395963481370030435541)
                ·
                  refine ⟨97603030394094610088333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4164395963481370030435541 97603030394094610088333)
                  ·
                    rfl

theorem cell23_1710731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 7].length) (baseStart_1710731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710731 prefixEnd_1710731 := by exact prefixLift 1710731
  have htrace : WordTrace (prefixWord ++ tailWord_1710731) baseStart_1710731 baseEnd_1710731 := by
    simpa [prefixWord, tailWord_1710731, baseEnd_1710731] using wordTrace_append hprefix tailTrace_1710731
  have hstable : (prefixWord ++ tailWord_1710731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710731).length < 2 ^ (prefixWord ++ tailWord_1710731).sum := by decide
  have hdescent : baseEnd_1710731 < baseStart_1710731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710746 : List Nat := [3, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2]
def baseStart_1710746 : Nat := 118140960795 + 1710746 * 2 ^ 59
def prefixEnd_1710746 : Nat := 4983230072969 + 3 ^ 40 * 1710746 * 2
def baseEnd_1710746 : Nat := 878434975756668932107429

theorem tailTrace_1710746 : CollatzResearch.WordTrace tailWord_1710746 prefixEnd_1710746 878434975756668932107429 := by
  unfold tailWord_1710746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599008165066722250224023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41597355106844592667264061 15599008165066722250224023)
  ·
    refine ⟨23398512247600083375336035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599008165066722250224023 23398512247600083375336035)
    ·
      refine ⟨35097768371400125063004053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23398512247600083375336035 35097768371400125063004053)
      ·
        refine ⟨1645207892409380862328315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35097768371400125063004053 1645207892409380862328315)
        ·
          refine ⟨2467811838614071293492473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645207892409380862328315 2467811838614071293492473)
          ·
            refine ⟨1850858878960553470119355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467811838614071293492473 1850858878960553470119355)
            ·
              refine ⟨2776288318440830205179033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850858878960553470119355 2776288318440830205179033)
              ·
                refine ⟨2082216238830622653884275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2776288318440830205179033 2082216238830622653884275)
                ·
                  refine ⟨3123324358245933980826413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082216238830622653884275 3123324358245933980826413)
                  ·
                    refine ⟨1171246634342225242809905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123324358245933980826413 1171246634342225242809905)
                    ·
                      refine ⟨878434975756668932107429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171246634342225242809905 878434975756668932107429)
                      ·
                        rfl

theorem cell23_1710746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_1710746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710746 prefixEnd_1710746 := by exact prefixLift 1710746
  have htrace : WordTrace (prefixWord ++ tailWord_1710746) baseStart_1710746 baseEnd_1710746 := by
    simpa [prefixWord, tailWord_1710746, baseEnd_1710746] using wordTrace_append hprefix tailTrace_1710746
  have hstable : (prefixWord ++ tailWord_1710746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710746).length < 2 ^ (prefixWord ++ tailWord_1710746).sum := by decide
  have hdescent : baseEnd_1710746 < baseStart_1710746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710759 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1710759 : Nat := 118140960795 + 1710759 * 2 ^ 59
def prefixEnd_1710759 : Nat := 4983230072969 + 3 ^ 40 * 1710759 * 2
def baseEnd_1710759 : Nat := 878441651005177381244869

theorem tailTrace_1710759 : CollatzResearch.WordTrace tailWord_1710759 prefixEnd_1710759 878441651005177381244869 := by
  unfold tailWord_1710759
  simp only [CollatzResearch.WordTrace]
  refine ⟨62396506809219792221119331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41597671206146528147412887 62396506809219792221119331)
  ·
    refine ⟨93594760213829688331678997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62396506809219792221119331 93594760213829688331678997)
    ·
      refine ⟨4387254385023266640547453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93594760213829688331678997 4387254385023266640547453)
      ·
        refine ⟨1645220394383724990205295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4387254385023266640547453 1645220394383724990205295)
        ·
          refine ⟨2467830591575587485307943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645220394383724990205295 2467830591575587485307943)
          ·
            refine ⟨3701745887363381227961915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467830591575587485307943 3701745887363381227961915)
            ·
              refine ⟨5552618831045071841942873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701745887363381227961915 5552618831045071841942873)
              ·
                refine ⟨4164464123283803881457155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5552618831045071841942873 4164464123283803881457155)
                ·
                  refine ⟨6246696184925705822185733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164464123283803881457155 6246696184925705822185733)
                  ·
                    refine ⟨1171255534673569841659825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6246696184925705822185733 1171255534673569841659825)
                    ·
                      refine ⟨878441651005177381244869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171255534673569841659825 878441651005177381244869)
                      ·
                        rfl

theorem cell23_1710759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1710759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710759 prefixEnd_1710759 := by exact prefixLift 1710759
  have htrace : WordTrace (prefixWord ++ tailWord_1710759) baseStart_1710759 baseEnd_1710759 := by
    simpa [prefixWord, tailWord_1710759, baseEnd_1710759] using wordTrace_append hprefix tailTrace_1710759
  have hstable : (prefixWord ++ tailWord_1710759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710759).length < 2 ^ (prefixWord ++ tailWord_1710759).sum := by decide
  have hdescent : baseEnd_1710759 < baseStart_1710759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710778 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_1710778 : Nat := 118140960795 + 1710778 * 2 ^ 59
def prefixEnd_1710778 : Nat := 4983230072969 + 3 ^ 40 * 1710778 * 2
def baseEnd_1710778 : Nat := 292817135712537602302427

theorem tailTrace_1710778 : CollatzResearch.WordTrace tailWord_1710778 prefixEnd_1710778 292817135712537602302427 := by
  unfold tailWord_1710778
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599299949037739616515247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41598133197433972310707325 15599299949037739616515247)
  ·
    refine ⟨23398949923556609424772871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599299949037739616515247 23398949923556609424772871)
    ·
      refine ⟨35098424885334914137159307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23398949923556609424772871 35098424885334914137159307)
      ·
        refine ⟨52647637328002371205738961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35098424885334914137159307 52647637328002371205738961)
        ·
          refine ⟨39485727996001778404304221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52647637328002371205738961 39485727996001778404304221)
          ·
            refine ⟨14807147998500666901614083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39485727996001778404304221 14807147998500666901614083)
            ·
              refine ⟨22210721997751000352421125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14807147998500666901614083 22210721997751000352421125)
              ·
                refine ⟨4164510374578312566078961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22210721997751000352421125 4164510374578312566078961)
                ·
                  refine ⟨3123382780933734424559221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164510374578312566078961 3123382780933734424559221)
                  ·
                    refine ⟨292817135712537602302427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3123382780933734424559221 292817135712537602302427)
                    ·
                      rfl

theorem cell23_1710778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_1710778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710778 prefixEnd_1710778 := by exact prefixLift 1710778
  have htrace : WordTrace (prefixWord ++ tailWord_1710778) baseStart_1710778 baseEnd_1710778 := by
    simpa [prefixWord, tailWord_1710778, baseEnd_1710778] using wordTrace_append hprefix tailTrace_1710778
  have hstable : (prefixWord ++ tailWord_1710778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710778).length < 2 ^ (prefixWord ++ tailWord_1710778).sum := by decide
  have hdescent : baseEnd_1710778 < baseStart_1710778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710812 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1710812 : Nat := 118140960795 + 1710812 * 2 ^ 59
def prefixEnd_1710812 : Nat := 4983230072969 + 3 ^ 40 * 1710812 * 2
def baseEnd_1710812 : Nat := 292822955159955224627375

theorem tailTrace_1710812 : CollatzResearch.WordTrace tailWord_1710812 prefixEnd_1710812 292822955159955224627375 := by
  unfold tailWord_1710812
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199219939013891136399345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41598959918685188181865793 31199219939013891136399345)
  ·
    refine ⟨23399414954260418352299509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31199219939013891136399345 23399414954260418352299509)
    ·
      refine ⟨2193695151961914220528079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23399414954260418352299509 2193695151961914220528079)
      ·
        refine ⟨3290542727942871330792119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193695151961914220528079 3290542727942871330792119)
        ·
          refine ⟨4935814091914306996188179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290542727942871330792119 4935814091914306996188179)
          ·
            refine ⟨7403721137871460494282269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4935814091914306996188179 7403721137871460494282269)
            ·
              refine ⟨2776395426701797685355851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7403721137871460494282269 2776395426701797685355851)
              ·
                refine ⟨4164593140052696528033777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776395426701797685355851 4164593140052696528033777)
                ·
                  refine ⟨3123444855039522396025333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164593140052696528033777 3123444855039522396025333)
                  ·
                    refine ⟨292822955159955224627375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3123444855039522396025333 292822955159955224627375)
                    ·
                      rfl

theorem cell23_1710812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1710812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710812 prefixEnd_1710812 := by exact prefixLift 1710812
  have htrace : WordTrace (prefixWord ++ tailWord_1710812) baseStart_1710812 baseEnd_1710812 := by
    simpa [prefixWord, tailWord_1710812, baseEnd_1710812] using wordTrace_append hprefix tailTrace_1710812
  have hstable : (prefixWord ++ tailWord_1710812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710812).length < 2 ^ (prefixWord ++ tailWord_1710812).sum := by decide
  have hdescent : baseEnd_1710812 < baseStart_1710812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710815 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_1710815 : Nat := 118140960795 + 1710815 * 2 ^ 59
def prefixEnd_1710815 : Nat := 4983230072969 + 3 ^ 40 * 1710815 * 2
def baseEnd_1710815 : Nat := 878470405921829162144611

theorem tailTrace_1710815 : CollatzResearch.WordTrace tailWord_1710815 prefixEnd_1710815 878470405921829162144611 := by
  unfold tailWord_1710815
  simp only [CollatzResearch.WordTrace]
  refine ⟨62398549297016913785157899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41599032864677942523438599 62398549297016913785157899)
  ·
    refine ⟨93597823945525370677736849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62398549297016913785157899 93597823945525370677736849)
    ·
      refine ⟨70198367959144028008302637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93597823945525370677736849 70198367959144028008302637)
      ·
        refine ⟨26324387984679010503113489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70198367959144028008302637 26324387984679010503113489)
        ·
          refine ⟨19743290988509257877335117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26324387984679010503113489 19743290988509257877335117)
          ·
            refine ⟨7403734120690971704000669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19743290988509257877335117 7403734120690971704000669)
            ·
              refine ⟨2776400295259114389000251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7403734120690971704000669 2776400295259114389000251)
              ·
                refine ⟨4164600442888671583500377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776400295259114389000251 4164600442888671583500377)
                ·
                  refine ⟨3123450332166503687625283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164600442888671583500377 3123450332166503687625283)
                  ·
                    refine ⟨4685175498249755531437925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3123450332166503687625283 4685175498249755531437925)
                    ·
                      refine ⟨878470405921829162144611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4685175498249755531437925 878470405921829162144611)
                      ·
                        rfl

theorem cell23_1710815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_1710815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710815 prefixEnd_1710815 := by exact prefixLift 1710815
  have htrace : WordTrace (prefixWord ++ tailWord_1710815) baseStart_1710815 baseEnd_1710815 := by
    simpa [prefixWord, tailWord_1710815, baseEnd_1710815] using wordTrace_append hprefix tailTrace_1710815
  have hstable : (prefixWord ++ tailWord_1710815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710815).length < 2 ^ (prefixWord ++ tailWord_1710815).sum := by decide
  have hdescent : baseEnd_1710815 < baseStart_1710815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710842 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 1, 4]
def baseStart_1710842 : Nat := 118140960795 + 1710842 * 2 ^ 59
def prefixEnd_1710842 : Nat := 4983230072969 + 3 ^ 40 * 1710842 * 2
def baseEnd_1710842 : Nat := 292828089966500185502329

theorem tailTrace_1710842 : CollatzResearch.WordTrace tailWord_1710842 prefixEnd_1710842 292828089966500185502329 := by
  unfold tailWord_1710842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15599883516979774349097695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41599689378612731597593853 15599883516979774349097695)
  ·
    refine ⟨23399825275469661523646543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15599883516979774349097695 23399825275469661523646543)
    ·
      refine ⟨35099737913204492285469815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23399825275469661523646543 35099737913204492285469815)
      ·
        refine ⟨52649606869806738428204723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35099737913204492285469815 52649606869806738428204723)
        ·
          refine ⟨78974410304710107642307085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52649606869806738428204723 78974410304710107642307085)
          ·
            refine ⟨29615403864266290365865157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78974410304710107642307085 29615403864266290365865157)
            ·
              refine ⟨5552888224549929443599717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29615403864266290365865157 5552888224549929443599717)
              ·
                refine ⟨1041166542103111770674947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5552888224549929443599717 1041166542103111770674947)
                ·
                  refine ⟨1561749813154667656012421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041166542103111770674947 1561749813154667656012421)
                  ·
                    refine ⟨292828089966500185502329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561749813154667656012421 292828089966500185502329)
                    ·
                      rfl

theorem cell23_1710842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 4].length) (baseStart_1710842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710842 prefixEnd_1710842 := by exact prefixLift 1710842
  have htrace : WordTrace (prefixWord ++ tailWord_1710842) baseStart_1710842 baseEnd_1710842 := by
    simpa [prefixWord, tailWord_1710842, baseEnd_1710842] using wordTrace_append hprefix tailTrace_1710842
  have hstable : (prefixWord ++ tailWord_1710842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710842).length < 2 ^ (prefixWord ++ tailWord_1710842).sum := by decide
  have hdescent : baseEnd_1710842 < baseStart_1710842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710848 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_1710848 : Nat := 118140960795 + 1710848 * 2 ^ 59
def prefixEnd_1710848 : Nat := 4983230072969 + 3 ^ 40 * 1710848 * 2
def baseEnd_1710848 : Nat := 878487350783427533031959

theorem tailTrace_1710848 : CollatzResearch.WordTrace tailWord_1710848 prefixEnd_1710848 878487350783427533031959 := by
  unfold tailWord_1710848
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199876452948680210554599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41599835270598240280739465 31199876452948680210554599)
  ·
    refine ⟨46799814679423020315831899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31199876452948680210554599 46799814679423020315831899)
    ·
      refine ⟨70199722019134530473747849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46799814679423020315831899 70199722019134530473747849)
      ·
        refine ⟨52649791514350897855310887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70199722019134530473747849 52649791514350897855310887)
        ·
          refine ⟨78974687271526346782966331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52649791514350897855310887 78974687271526346782966331)
          ·
            refine ⟨118462030907289520174449497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78974687271526346782966331 118462030907289520174449497)
            ·
              refine ⟨88846523180467140130837123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118462030907289520174449497 88846523180467140130837123)
              ·
                refine ⟨133269784770700710196255685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88846523180467140130837123 133269784770700710196255685)
                ·
                  refine ⟨24988084644506383161797941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133269784770700710196255685 24988084644506383161797941)
                  ·
                    refine ⟨2342632935422473421418557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24988084644506383161797941 2342632935422473421418557)
                    ·
                      refine ⟨878487350783427533031959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2342632935422473421418557 878487350783427533031959)
                      ·
                        rfl

theorem cell23_1710848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_1710848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710848 prefixEnd_1710848 := by exact prefixLift 1710848
  have htrace : WordTrace (prefixWord ++ tailWord_1710848) baseStart_1710848 baseEnd_1710848 := by
    simpa [prefixWord, tailWord_1710848, baseEnd_1710848] using wordTrace_append hprefix tailTrace_1710848
  have hstable : (prefixWord ++ tailWord_1710848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710848).length < 2 ^ (prefixWord ++ tailWord_1710848).sum := by decide
  have hdescent : baseEnd_1710848 < baseStart_1710848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710858 : List Nat := [3, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1710858 : Nat := 118140960795 + 1710858 * 2 ^ 59
def prefixEnd_1710858 : Nat := 4983230072969 + 3 ^ 40 * 1710858 * 2
def baseEnd_1710858 : Nat := 878492485589972493906913

theorem tailTrace_1710858 : CollatzResearch.WordTrace tailWord_1710858 prefixEnd_1710858 878492485589972493906913 := by
  unfold tailWord_1710858
  simp only [CollatzResearch.WordTrace]
  refine ⟨15600029408965283032243307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41600078423907421419315485 15600029408965283032243307)
  ·
    refine ⟨23400044113447924548364961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15600029408965283032243307 23400044113447924548364961)
    ·
      refine ⟨17550033085085943411273721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23400044113447924548364961 17550033085085943411273721)
      ·
        refine ⟨13162524813814457558455291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17550033085085943411273721 13162524813814457558455291)
        ·
          refine ⟨19743787220721686337682937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162524813814457558455291 19743787220721686337682937)
          ·
            refine ⟨14807840415541264753262203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19743787220721686337682937 14807840415541264753262203)
            ·
              refine ⟨22211760623311897129893305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14807840415541264753262203 22211760623311897129893305)
              ·
                refine ⟨16658820467483922847419979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22211760623311897129893305 16658820467483922847419979)
                ·
                  refine ⟨24988230701225884271129969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16658820467483922847419979 24988230701225884271129969)
                  ·
                    refine ⟨18741173025919413203347477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24988230701225884271129969 18741173025919413203347477)
                    ·
                      refine ⟨878492485589972493906913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18741173025919413203347477 878492485589972493906913)
                      ·
                        rfl

theorem cell23_1710858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1710858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710858 prefixEnd_1710858 := by exact prefixLift 1710858
  have htrace : WordTrace (prefixWord ++ tailWord_1710858) baseStart_1710858 baseEnd_1710858 := by
    simpa [prefixWord, tailWord_1710858, baseEnd_1710858] using wordTrace_append hprefix tailTrace_1710858
  have hstable : (prefixWord ++ tailWord_1710858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710858).length < 2 ^ (prefixWord ++ tailWord_1710858).sum := by decide
  have hdescent : baseEnd_1710858 < baseStart_1710858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710885 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_1710885 : Nat := 118140960795 + 1710885 * 2 ^ 59
def prefixEnd_1710885 : Nat := 4983230072969 + 3 ^ 40 * 1710885 * 2
def baseEnd_1710885 : Nat := 292835449855881296089763

theorem tailTrace_1710885 : CollatzResearch.WordTrace tailWord_1710885 prefixEnd_1710885 292835449855881296089763 := by
  unfold tailWord_1710885
  simp only [CollatzResearch.WordTrace]
  refine ⟨62401102406763315740206109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41600734937842210493470739 62401102406763315740206109)
  ·
    refine ⟨23400413402536243402577291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62401102406763315740206109 23400413402536243402577291)
    ·
      refine ⟨35100620103804365103865937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23400413402536243402577291 35100620103804365103865937)
      ·
        refine ⟨26325465077853273827899453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35100620103804365103865937 26325465077853273827899453)
        ·
          refine ⟨9872049404194977685462295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26325465077853273827899453 9872049404194977685462295)
          ·
            refine ⟨14808074106292466528193443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872049404194977685462295 14808074106292466528193443)
            ·
              refine ⟨22212111159438699792290165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14808074106292466528193443 22212111159438699792290165)
              ·
                refine ⟨2082385421197378105527203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22212111159438699792290165 2082385421197378105527203)
                ·
                  refine ⟨3123578131796067158290805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082385421197378105527203 3123578131796067158290805)
                  ·
                    refine ⟨292835449855881296089763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3123578131796067158290805 292835449855881296089763)
                    ·
                      rfl

theorem cell23_1710885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_1710885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710885 prefixEnd_1710885 := by exact prefixLift 1710885
  have htrace : WordTrace (prefixWord ++ tailWord_1710885) baseStart_1710885 baseEnd_1710885 := by
    simpa [prefixWord, tailWord_1710885, baseEnd_1710885] using wordTrace_append hprefix tailTrace_1710885
  have hstable : (prefixWord ++ tailWord_1710885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710885).length < 2 ^ (prefixWord ++ tailWord_1710885).sum := by decide
  have hdescent : baseEnd_1710885 < baseStart_1710885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710892 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_1710892 : Nat := 118140960795 + 1710892 * 2 ^ 59
def prefixEnd_1710892 : Nat := 4983230072969 + 3 ^ 40 * 1710892 * 2
def baseEnd_1710892 : Nat := 878509943932225360881757

theorem tailTrace_1710892 : CollatzResearch.WordTrace tailWord_1710892 prefixEnd_1710892 878509943932225360881757 := by
  unfold tailWord_1710892
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200678858868977967855465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41600905145158637290473953 31200678858868977967855465)
  ·
    refine ⟨23400509144151733475891599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31200678858868977967855465 23400509144151733475891599)
    ·
      refine ⟨35100763716227600213837399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23400509144151733475891599 35100763716227600213837399)
      ·
        refine ⟨52651145574341400320756099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35100763716227600213837399 52651145574341400320756099)
        ·
          refine ⟨78976718361512100481134149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52651145574341400320756099 78976718361512100481134149)
          ·
            refine ⟨14808134692783518840212653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78976718361512100481134149 14808134692783518840212653)
            ·
              refine ⟨5553050509793819565079745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14808134692783518840212653 5553050509793819565079745)
              ·
                refine ⟨4164787882345364673809809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553050509793819565079745 4164787882345364673809809)
                ·
                  refine ⟨3123590911759023505357357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4164787882345364673809809 3123590911759023505357357)
                  ·
                    refine ⟨1171346591909633814509009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123590911759023505357357 1171346591909633814509009)
                    ·
                      refine ⟨878509943932225360881757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171346591909633814509009 878509943932225360881757)
                      ·
                        rfl

theorem cell23_1710892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_1710892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710892 prefixEnd_1710892 := by exact prefixLift 1710892
  have htrace : WordTrace (prefixWord ++ tailWord_1710892) baseStart_1710892 baseEnd_1710892 := by
    simpa [prefixWord, tailWord_1710892, baseEnd_1710892] using wordTrace_append hprefix tailTrace_1710892
  have hstable : (prefixWord ++ tailWord_1710892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710892).length < 2 ^ (prefixWord ++ tailWord_1710892).sum := by decide
  have hdescent : baseEnd_1710892 < baseStart_1710892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710893 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1710893 : Nat := 118140960795 + 1710893 * 2 ^ 59
def prefixEnd_1710893 : Nat := 4983230072969 + 3 ^ 40 * 1710893 * 2
def baseEnd_1710893 : Nat := 292836819137626618989751

theorem tailTrace_1710893 : CollatzResearch.WordTrace tailWord_1710893 prefixEnd_1710893 292836819137626618989751 := by
  unfold tailWord_1710893
  simp only [CollatzResearch.WordTrace]
  refine ⟨62401394190734333106497333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41600929460489555404331555 62401394190734333106497333)
  ·
    refine ⟨5850130705381343728734125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62401394190734333106497333 5850130705381343728734125)
    ·
      refine ⟨2193799014518003898275297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5850130705381343728734125 2193799014518003898275297)
      ·
        refine ⟨1645349260888502923706473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2193799014518003898275297 1645349260888502923706473)
        ·
          refine ⟨1234011945666377192779855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645349260888502923706473 1234011945666377192779855)
          ·
            refine ⟨1851017918499565789169783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234011945666377192779855 1851017918499565789169783)
            ·
              refine ⟨2776526877749348683754675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851017918499565789169783 2776526877749348683754675)
              ·
                refine ⟨4164790316624023025632013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776526877749348683754675 4164790316624023025632013)
                ·
                  refine ⟨1561796368734008634612005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4164790316624023025632013 1561796368734008634612005)
                  ·
                    refine ⟨292836819137626618989751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1561796368734008634612005 292836819137626618989751)
                    ·
                      rfl

theorem cell23_1710893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1710893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710893 prefixEnd_1710893 := by exact prefixLift 1710893
  have htrace : WordTrace (prefixWord ++ tailWord_1710893) baseStart_1710893 baseEnd_1710893 := by
    simpa [prefixWord, tailWord_1710893, baseEnd_1710893] using wordTrace_append hprefix tailTrace_1710893
  have hstable : (prefixWord ++ tailWord_1710893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710893).length < 2 ^ (prefixWord ++ tailWord_1710893).sum := by decide
  have hdescent : baseEnd_1710893 < baseStart_1710893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710899 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 3]
def baseStart_1710899 : Nat := 118140960795 + 1710899 * 2 ^ 59
def prefixEnd_1710899 : Nat := 4983230072969 + 3 ^ 40 * 1710899 * 2
def baseEnd_1710899 : Nat := 878513538296806833494225

theorem tailTrace_1710899 : CollatzResearch.WordTrace tailWord_1710899 prefixEnd_1710899 878513538296806833494225 := by
  unfold tailWord_1710899
  simp only [CollatzResearch.WordTrace]
  refine ⟨62401613028712596131215751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41601075352475064087477167 62401613028712596131215751)
  ·
    refine ⟨93602419543068894196823627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62401613028712596131215751 93602419543068894196823627)
    ·
      refine ⟨140403629314603341295235441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93602419543068894196823627 140403629314603341295235441)
      ·
        refine ⟨105302721985952505971426581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140403629314603341295235441 105302721985952505971426581)
        ·
          refine ⟨4936065093091523717410621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105302721985952505971426581 4936065093091523717410621)
          ·
            refine ⟨1851024409909321394028983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4936065093091523717410621 1851024409909321394028983)
            ·
              refine ⟨2776536614863982091043475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851024409909321394028983 2776536614863982091043475)
              ·
                refine ⟨4164804922295973136565213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776536614863982091043475 4164804922295973136565213)
                ·
                  refine ⟨1561801845860989926211955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4164804922295973136565213 1561801845860989926211955)
                  ·
                    refine ⟨2342702768791484889317933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1561801845860989926211955 2342702768791484889317933)
                    ·
                      refine ⟨878513538296806833494225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2342702768791484889317933 878513538296806833494225)
                      ·
                        rfl

theorem cell23_1710899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 1, 3].length) (baseStart_1710899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710899 prefixEnd_1710899 := by exact prefixLift 1710899
  have htrace : WordTrace (prefixWord ++ tailWord_1710899) baseStart_1710899 baseEnd_1710899 := by
    simpa [prefixWord, tailWord_1710899, baseEnd_1710899] using wordTrace_append hprefix tailTrace_1710899
  have hstable : (prefixWord ++ tailWord_1710899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710899).length < 2 ^ (prefixWord ++ tailWord_1710899).sum := by decide
  have hdescent : baseEnd_1710899 < baseStart_1710899 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710928 : List Nat := [2, 1, 1, 1, 1, 4, 4, 9]
def baseStart_1710928 : Nat := 118140960795 + 1710928 * 2 ^ 59
def prefixEnd_1710928 : Nat := 4983230072969 + 3 ^ 40 * 1710928 * 2
def baseEnd_1710928 : Nat := 32538089971695822964133

theorem tailTrace_1710928 : CollatzResearch.WordTrace tailWord_1710928 prefixEnd_1710928 32538089971695822964133 := by
  unfold tailWord_1710928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31201335372803767042010719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41601780497071689389347625 31201335372803767042010719)
  ·
    refine ⟨46802003059205650563016079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31201335372803767042010719 46802003059205650563016079)
    ·
      refine ⟨70203004588808475844524119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46802003059205650563016079 70203004588808475844524119)
      ·
        refine ⟨105304506883212713766786179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70203004588808475844524119 105304506883212713766786179)
        ·
          refine ⟨157956760324819070650179269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105304506883212713766786179 157956760324819070650179269)
          ·
            refine ⟨29616892560903575746908613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157956760324819070650179269 29616892560903575746908613)
            ·
              refine ⟨5553167355169420452545365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29616892560903575746908613 5553167355169420452545365)
              ·
                refine ⟨32538089971695822964133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5553167355169420452545365 32538089971695822964133)
                ·
                  rfl

theorem cell23_1710928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 9].length) (baseStart_1710928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710928 prefixEnd_1710928 := by exact prefixLift 1710928
  have htrace : WordTrace (prefixWord ++ tailWord_1710928) baseStart_1710928 baseEnd_1710928 := by
    simpa [prefixWord, tailWord_1710928, baseEnd_1710928] using wordTrace_append hprefix tailTrace_1710928
  have hstable : (prefixWord ++ tailWord_1710928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710928).length < 2 ^ (prefixWord ++ tailWord_1710928).sum := by decide
  have hdescent : baseEnd_1710928 < baseStart_1710928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710932 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1710932 : Nat := 118140960795 + 1710932 * 2 ^ 59
def prefixEnd_1710932 : Nat := 4983230072969 + 3 ^ 40 * 1710932 * 2
def baseEnd_1710932 : Nat := 292843494386135068127191

theorem tailTrace_1710932 : CollatzResearch.WordTrace tailWord_1710932 prefixEnd_1710932 292843494386135068127191 := by
  unfold tailWord_1710932
  simp only [CollatzResearch.WordTrace]
  refine ⟨31201408318796521383583525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41601877758395361844778033 31201408318796521383583525)
  ·
    refine ⟨5850264059774347759421911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31201408318796521383583525 5850264059774347759421911)
    ·
      refine ⟨8775396089661521639132867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850264059774347759421911 8775396089661521639132867)
      ·
        refine ⟨13163094134492282458699301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775396089661521639132867 13163094134492282458699301)
        ·
          refine ⟨2468080150217302961006119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13163094134492282458699301 2468080150217302961006119)
          ·
            refine ⟨3702120225325954441509179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468080150217302961006119 3702120225325954441509179)
            ·
              refine ⟨5553180337988931662263769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702120225325954441509179 5553180337988931662263769)
              ·
                refine ⟨4164885253491698746697827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553180337988931662263769 4164885253491698746697827)
                ·
                  refine ⟨6247327880237548120046741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4164885253491698746697827 6247327880237548120046741)
                  ·
                    refine ⟨292843494386135068127191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6247327880237548120046741 292843494386135068127191)
                    ·
                      rfl

theorem cell23_1710932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1710932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710932 prefixEnd_1710932 := by exact prefixLift 1710932
  have htrace : WordTrace (prefixWord ++ tailWord_1710932) baseStart_1710932 baseEnd_1710932 := by
    simpa [prefixWord, tailWord_1710932, baseEnd_1710932] using wordTrace_append hprefix tailTrace_1710932
  have hstable : (prefixWord ++ tailWord_1710932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710932).length < 2 ^ (prefixWord ++ tailWord_1710932).sum := by decide
  have hdescent : baseEnd_1710932 < baseStart_1710932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710935 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_1710935 : Nat := 118140960795 + 1710935 * 2 ^ 59
def prefixEnd_1710935 : Nat := 4983230072969 + 3 ^ 40 * 1710935 * 2
def baseEnd_1710935 : Nat := 878532023600368692644059

theorem tailTrace_1710935 : CollatzResearch.WordTrace tailWord_1710935 prefixEnd_1710935 878532023600368692644059 := by
  unfold tailWord_1710935
  simp only [CollatzResearch.WordTrace]
  refine ⟨62402926056582174279526259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41601950704388116186350839 62402926056582174279526259)
  ·
    refine ⟨93604389084873261419289389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62402926056582174279526259 93604389084873261419289389)
    ·
      refine ⟨35101645906827473032233521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93604389084873261419289389 35101645906827473032233521)
      ·
        refine ⟨26326234430120604774175141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35101645906827473032233521 26326234430120604774175141)
        ·
          refine ⟨4936168955647613395157839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26326234430120604774175141 4936168955647613395157839)
          ·
            refine ⟨7404253433471420092736759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936168955647613395157839 7404253433471420092736759)
            ·
              refine ⟨11106380150207130139105139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7404253433471420092736759 11106380150207130139105139)
              ·
                refine ⟨16659570225310695208657709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11106380150207130139105139 16659570225310695208657709)
                ·
                  refine ⟨6247338834491510703246641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16659570225310695208657709 6247338834491510703246641)
                  ·
                    refine ⟨4685504125868633027434981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6247338834491510703246641 4685504125868633027434981)
                    ·
                      refine ⟨878532023600368692644059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4685504125868633027434981 878532023600368692644059)
                      ·
                        rfl

theorem cell23_1710935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_1710935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710935 prefixEnd_1710935 := by exact prefixLift 1710935
  have htrace : WordTrace (prefixWord ++ tailWord_1710935) baseStart_1710935 baseEnd_1710935 := by
    simpa [prefixWord, tailWord_1710935, baseEnd_1710935] using wordTrace_append hprefix tailTrace_1710935
  have hstable : (prefixWord ++ tailWord_1710935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710935).length < 2 ^ (prefixWord ++ tailWord_1710935).sum := by decide
  have hdescent : baseEnd_1710935 < baseStart_1710935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710956 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 1, 2, 2]
def baseStart_1710956 : Nat := 118140960795 + 1710956 * 2 ^ 59
def prefixEnd_1710956 : Nat := 4983230072969 + 3 ^ 40 * 1710956 * 2
def baseEnd_1710956 : Nat := 878542806694113110481463

theorem tailTrace_1710956 : CollatzResearch.WordTrace tailWord_1710956 prefixEnd_1710956 878542806694113110481463 := by
  unfold tailWord_1710956
  simp only [CollatzResearch.WordTrace]
  refine ⟨31201845994753047433020361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41602461326337396577360481 31201845994753047433020361)
  ·
    refine ⟨23401384496064785574765271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31201845994753047433020361 23401384496064785574765271)
    ·
      refine ⟨35102076744097178362147907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23401384496064785574765271 35102076744097178362147907)
      ·
        refine ⟨52653115116145767543221861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35102076744097178362147907 52653115116145767543221861)
        ·
          refine ⟨9872459084277331414354099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52653115116145767543221861 9872459084277331414354099)
          ·
            refine ⟨14808688626415997121531149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872459084277331414354099 14808688626415997121531149)
            ·
              refine ⟨5553258234905998920574181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14808688626415997121531149 5553258234905998920574181)
              ·
                refine ⟨1041235919044874797607659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5553258234905998920574181 1041235919044874797607659)
                ·
                  refine ⟨1561853878567312196411489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041235919044874797607659 1561853878567312196411489)
                  ·
                    refine ⟨1171390408925484147308617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1561853878567312196411489 1171390408925484147308617)
                    ·
                      refine ⟨878542806694113110481463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171390408925484147308617 878542806694113110481463)
                      ·
                        rfl

theorem cell23_1710956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_1710956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710956 prefixEnd_1710956 := by exact prefixLift 1710956
  have htrace : WordTrace (prefixWord ++ tailWord_1710956) baseStart_1710956 baseEnd_1710956 := by
    simpa [prefixWord, tailWord_1710956, baseEnd_1710956] using wordTrace_append hprefix tailTrace_1710956
  have hstable : (prefixWord ++ tailWord_1710956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710956).length < 2 ^ (prefixWord ++ tailWord_1710956).sum := by decide
  have hdescent : baseEnd_1710956 < baseStart_1710956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1710999 : List Nat := [1, 1, 3, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_1710999 : Nat := 118140960795 + 1710999 * 2 ^ 59
def prefixEnd_1710999 : Nat := 4983230072969 + 3 ^ 40 * 1710999 * 2
def baseEnd_1710999 : Nat := 878564886362256442243765

theorem tailTrace_1710999 : CollatzResearch.WordTrace tailWord_1710999 prefixEnd_1710999 878564886362256442243765 := by
  unfold tailWord_1710999
  simp only [CollatzResearch.WordTrace]
  refine ⟨62405260328350313209856051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41603506885566875473237367 62405260328350313209856051)
  ·
    refine ⟨93607890492525469814784077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62405260328350313209856051 93607890492525469814784077)
    ·
      refine ⟨35102958934697051180544029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93607890492525469814784077 35102958934697051180544029)
      ·
        refine ⟨13163609600511394192704011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35102958934697051180544029 13163609600511394192704011)
        ·
          refine ⟨19745414400767091289056017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13163609600511394192704011 19745414400767091289056017)
          ·
            refine ⟨14809060800575318466792013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19745414400767091289056017 14809060800575318466792013)
            ·
              refine ⟨5553397800215744425047005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14809060800575318466792013 5553397800215744425047005)
              ·
                refine ⟨2082524175080904159392627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5553397800215744425047005 2082524175080904159392627)
                ·
                  refine ⟨3123786262621356239088941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082524175080904159392627 3123786262621356239088941)
                  ·
                    refine ⟨1171419848483008589658353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3123786262621356239088941 1171419848483008589658353)
                    ·
                      refine ⟨878564886362256442243765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171419848483008589658353 878564886362256442243765)
                      ·
                        rfl

theorem cell23_1710999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_1710999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1710999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1710999 prefixEnd_1710999 := by exact prefixLift 1710999
  have htrace : WordTrace (prefixWord ++ tailWord_1710999) baseStart_1710999 baseEnd_1710999 := by
    simpa [prefixWord, tailWord_1710999, baseEnd_1710999] using wordTrace_append hprefix tailTrace_1710999
  have hstable : (prefixWord ++ tailWord_1710999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1710999).length < 2 ^ (prefixWord ++ tailWord_1710999).sum := by decide
  have hdescent : baseEnd_1710999 < baseStart_1710999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1710999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711005 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1711005 : Nat := 118140960795 + 1711005 * 2 ^ 59
def prefixEnd_1711005 : Nat := 4983230072969 + 3 ^ 40 * 1711005 * 2
def baseEnd_1711005 : Nat := 292855989082061139589579

theorem tailTrace_1711005 : CollatzResearch.WordTrace tailWord_1711005 prefixEnd_1711005 292855989082061139589579 := by
  unfold tailWord_1711005
  simp only [CollatzResearch.WordTrace]
  refine ⟨62405479166328576234574469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41603652777552384156382979 62405479166328576234574469)
  ·
    refine ⟨11701027343686608043982713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62405479166328576234574469 11701027343686608043982713)
    ·
      refine ⟨8775770507764956032987035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11701027343686608043982713 8775770507764956032987035)
      ·
        refine ⟨13163655761647434049480553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775770507764956032987035 13163655761647434049480553)
        ·
          refine ⟨9872741821235575537110415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13163655761647434049480553 9872741821235575537110415)
          ·
            refine ⟨14809112731853363305665623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9872741821235575537110415 14809112731853363305665623)
            ·
              refine ⟨22213669097780044958498435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14809112731853363305665623 22213669097780044958498435)
              ·
                refine ⟨33320503646670067437747653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22213669097780044958498435 33320503646670067437747653)
                ·
                  refine ⟨6247594433750637644577685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33320503646670067437747653 6247594433750637644577685)
                  ·
                    refine ⟨292855989082061139589579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6247594433750637644577685 292855989082061139589579)
                    ·
                      rfl

theorem cell23_1711005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1711005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711005 prefixEnd_1711005 := by exact prefixLift 1711005
  have htrace : WordTrace (prefixWord ++ tailWord_1711005) baseStart_1711005 baseEnd_1711005 := by
    simpa [prefixWord, tailWord_1711005, baseEnd_1711005] using wordTrace_append hprefix tailTrace_1711005
  have hstable : (prefixWord ++ tailWord_1711005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711005).length < 2 ^ (prefixWord ++ tailWord_1711005).sum := by decide
  have hdescent : baseEnd_1711005 < baseStart_1711005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711030 : List Nat := [5, 1, 4, 1, 2, 1, 2, 7]
def baseStart_1711030 : Nat := 118140960795 + 1711030 * 2 ^ 59
def prefixEnd_1711030 : Nat := 4983230072969 + 3 ^ 40 * 1711030 * 2
def baseEnd_1711030 : Nat := 32540029787501697072449

theorem tailTrace_1711030 : CollatzResearch.WordTrace tailWord_1711030 prefixEnd_1711030 32540029787501697072449 := by
  unfold tailWord_1711030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3900399436952375344014659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41604260660825337002823029 3900399436952375344014659)
  ·
    refine ⟨5850599155428563016021989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3900399436952375344014659 5850599155428563016021989)
    ·
      refine ⟨1096987341642855565504123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5850599155428563016021989 1096987341642855565504123)
      ·
        refine ⟨1645481012464283348256185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096987341642855565504123 1645481012464283348256185)
        ·
          refine ⟨1234110759348212511192139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1645481012464283348256185 1234110759348212511192139)
          ·
            refine ⟨1851166139022318766788209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234110759348212511192139 1851166139022318766788209)
            ·
              refine ⟨1388374604266739075091157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851166139022318766788209 1388374604266739075091157)
              ·
                refine ⟨32540029787501697072449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1388374604266739075091157 32540029787501697072449)
                ·
                  rfl

theorem cell23_1711030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 7].length) (baseStart_1711030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711030 prefixEnd_1711030 := by exact prefixLift 1711030
  have htrace : WordTrace (prefixWord ++ tailWord_1711030) baseStart_1711030 baseEnd_1711030 := by
    simpa [prefixWord, tailWord_1711030, baseEnd_1711030] using wordTrace_append hprefix tailTrace_1711030
  have hstable : (prefixWord ++ tailWord_1711030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711030).length < 2 ^ (prefixWord ++ tailWord_1711030).sum := by decide
  have hdescent : baseEnd_1711030 < baseStart_1711030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711069 : List Nat := [1, 4, 3, 1, 2, 3, 1, 1, 7]
def baseStart_1711069 : Nat := 118140960795 + 1711069 * 2 ^ 59
def prefixEnd_1711069 : Nat := 4983230072969 + 3 ^ 40 * 1711069 * 2
def baseEnd_1711069 : Nat := 97622314445341240929827

theorem tailTrace_1711069 : CollatzResearch.WordTrace tailWord_1711069 prefixEnd_1711069 97622314445341240929827 := by
  unfold tailWord_1711069
  simp only [CollatzResearch.WordTrace]
  refine ⟨62407813438096715164904261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41605208958731143443269507 62407813438096715164904261)
  ·
    refine ⟨11701465019643134093419549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62407813438096715164904261 11701465019643134093419549)
    ·
      refine ⟨4388049382366175285032331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11701465019643134093419549 4388049382366175285032331)
      ·
        refine ⟨6582074073549262927548497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4388049382366175285032331 6582074073549262927548497)
        ·
          refine ⟨4936555555161947195661373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6582074073549262927548497 4936555555161947195661373)
          ·
            refine ⟨1851208333185730198373015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4936555555161947195661373 1851208333185730198373015)
            ·
              refine ⟨2776812499778595297559523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851208333185730198373015 2776812499778595297559523)
              ·
                refine ⟨4165218749667892946339285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2776812499778595297559523 4165218749667892946339285)
                ·
                  refine ⟨97622314445341240929827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4165218749667892946339285 97622314445341240929827)
                  ·
                    rfl

theorem cell23_1711069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_1711069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711069 prefixEnd_1711069 := by exact prefixLift 1711069
  have htrace : WordTrace (prefixWord ++ tailWord_1711069) baseStart_1711069 baseEnd_1711069 := by
    simpa [prefixWord, tailWord_1711069, baseEnd_1711069] using wordTrace_append hprefix tailTrace_1711069
  have hstable : (prefixWord ++ tailWord_1711069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711069).length < 2 ^ (prefixWord ++ tailWord_1711069).sum := by decide
  have hdescent : baseEnd_1711069 < baseStart_1711069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711146 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1711146 : Nat := 118140960795 + 1711146 * 2 ^ 59
def prefixEnd_1711146 : Nat := 4983230072969 + 3 ^ 40 * 1711146 * 2
def baseEnd_1711146 : Nat := 292880122672822455701863

theorem tailTrace_1711146 : CollatzResearch.WordTrace tailWord_1711146 prefixEnd_1711146 292880122672822455701863 := by
  unfold tailWord_1711146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15602655464704439328864323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41607081239211838210304861 15602655464704439328864323)
  ·
    refine ⟨23403983197056658993296485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15602655464704439328864323 23403983197056658993296485)
    ·
      refine ⟨4388246849448123561243091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23403983197056658993296485 4388246849448123561243091)
      ·
        refine ⟨6582370274172185341864637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4388246849448123561243091 6582370274172185341864637)
        ·
          refine ⟨2468388852814569503199239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6582370274172185341864637 2468388852814569503199239)
          ·
            refine ⟨3702583279221854254798859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468388852814569503199239 3702583279221854254798859)
            ·
              refine ⟨5553874918832781382198289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702583279221854254798859 5553874918832781382198289)
              ·
                refine ⟨4165406189124586036648717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5553874918832781382198289 4165406189124586036648717)
                ·
                  refine ⟨1562027320921719763743269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4165406189124586036648717 1562027320921719763743269)
                  ·
                    refine ⟨292880122672822455701863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1562027320921719763743269 292880122672822455701863)
                    ·
                      rfl

theorem cell23_1711146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1711146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711146 prefixEnd_1711146 := by exact prefixLift 1711146
  have htrace : WordTrace (prefixWord ++ tailWord_1711146) baseStart_1711146 baseEnd_1711146 := by
    simpa [prefixWord, tailWord_1711146, baseEnd_1711146] using wordTrace_append hprefix tailTrace_1711146
  have hstable : (prefixWord ++ tailWord_1711146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711146).length < 2 ^ (prefixWord ++ tailWord_1711146).sum := by decide
  have hdescent : baseEnd_1711146 < baseStart_1711146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711156 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_1711156 : Nat := 118140960795 + 1711156 * 2 ^ 59
def prefixEnd_1711156 : Nat := 4983230072969 + 3 ^ 40 * 1711156 * 2
def baseEnd_1711156 : Nat := 878645502825012327980543

theorem tailTrace_1711156 : CollatzResearch.WordTrace tailWord_1711156 prefixEnd_1711156 878645502825012327980543 := by
  unfold tailWord_1711156
  simp only [CollatzResearch.WordTrace]
  refine ⟨31205493294390764511660661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41607324392521019348880881 31205493294390764511660661)
  ·
    refine ⟨2925514996349134172968187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31205493294390764511660661 2925514996349134172968187)
    ·
      refine ⟨4388272494523701259452281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2925514996349134172968187 4388272494523701259452281)
      ·
        refine ⟨3291204370892775944589211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4388272494523701259452281 3291204370892775944589211)
        ·
          refine ⟨4936806556339163916883817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291204370892775944589211 4936806556339163916883817)
          ·
            refine ⟨3702604917254372937662863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936806556339163916883817 3702604917254372937662863)
            ·
              refine ⟨5553907375881559406494295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3702604917254372937662863 5553907375881559406494295)
              ·
                refine ⟨8330861063822339109741443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5553907375881559406494295 8330861063822339109741443)
                ·
                  refine ⟨12496291595733508664612165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8330861063822339109741443 12496291595733508664612165)
                  ·
                    refine ⟨2343054674200032874614781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12496291595733508664612165 2343054674200032874614781)
                    ·
                      refine ⟨878645502825012327980543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2343054674200032874614781 878645502825012327980543)
                      ·
                        rfl

theorem cell23_1711156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_1711156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711156 prefixEnd_1711156 := by exact prefixLift 1711156
  have htrace : WordTrace (prefixWord ++ tailWord_1711156) baseStart_1711156 baseEnd_1711156 := by
    simpa [prefixWord, tailWord_1711156, baseEnd_1711156] using wordTrace_append hprefix tailTrace_1711156
  have hstable : (prefixWord ++ tailWord_1711156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711156).length < 2 ^ (prefixWord ++ tailWord_1711156).sum := by decide
  have hdescent : baseEnd_1711156 < baseStart_1711156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711186 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_1711186 : Nat := 118140960795 + 1711186 * 2 ^ 59
def prefixEnd_1711186 : Nat := 4983230072969 + 3 ^ 40 * 1711186 * 2
def baseEnd_1711186 : Nat := 878660907244647210605405

theorem tailTrace_1711186 : CollatzResearch.WordTrace tailWord_1711186 prefixEnd_1711186 878660907244647210605405 := by
  unfold tailWord_1711186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15603020194668211036728353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41608053852448562764608941 15603020194668211036728353)
  ·
    refine ⟨11702265146001158277546265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15603020194668211036728353 11702265146001158277546265)
    ·
      refine ⟨8776698859500868708159699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11702265146001158277546265 8776698859500868708159699)
      ·
        refine ⟨13165048289251303062239549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8776698859500868708159699 13165048289251303062239549)
        ·
          refine ⟨4936893108469238648339831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13165048289251303062239549 4936893108469238648339831)
          ·
            refine ⟨7405339662703857972509747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4936893108469238648339831 7405339662703857972509747)
            ·
              refine ⟨11108009494055786958764621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7405339662703857972509747 11108009494055786958764621)
              ·
                refine ⟨4165503560270920109536733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11108009494055786958764621 4165503560270920109536733)
                ·
                  refine ⟨1562063835101595041076275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4165503560270920109536733 1562063835101595041076275)
                  ·
                    refine ⟨2343095752652392561614413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562063835101595041076275 2343095752652392561614413)
                    ·
                      refine ⟨878660907244647210605405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2343095752652392561614413 878660907244647210605405)
                      ·
                        rfl

theorem cell23_1711186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_1711186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711186 prefixEnd_1711186 := by exact prefixLift 1711186
  have htrace : WordTrace (prefixWord ++ tailWord_1711186) baseStart_1711186 baseEnd_1711186 := by
    simpa [prefixWord, tailWord_1711186, baseEnd_1711186] using wordTrace_append hprefix tailTrace_1711186
  have hstable : (prefixWord ++ tailWord_1711186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711186).length < 2 ^ (prefixWord ++ tailWord_1711186).sum := by decide
  have hdescent : baseEnd_1711186 < baseStart_1711186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711209 : List Nat := [1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_1711209 : Nat := 118140960795 + 1711209 * 2 ^ 59
def prefixEnd_1711209 : Nat := 4983230072969 + 3 ^ 40 * 1711209 * 2
def baseEnd_1711209 : Nat := 878672717299700620617799

theorem tailTrace_1711209 : CollatzResearch.WordTrace tailWord_1711209 prefixEnd_1711209 878672717299700620617799 := by
  unfold tailWord_1711209
  simp only [CollatzResearch.WordTrace]
  refine ⟨62412919657589519075000681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41608613105059679383333787 62412919657589519075000681)
  ·
    refine ⟨46809689743192139306250511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62412919657589519075000681 46809689743192139306250511)
    ·
      refine ⟨70214534614788208959375767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46809689743192139306250511 70214534614788208959375767)
      ·
        refine ⟨105321801922182313439063651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70214534614788208959375767 105321801922182313439063651)
        ·
          refine ⟨157982702883273470158595477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105321801922182313439063651 157982702883273470158595477)
          ·
            refine ⟨7405439197653443913684163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157982702883273470158595477 7405439197653443913684163)
            ·
              refine ⟨11108158796480165870526245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7405439197653443913684163 11108158796480165870526245)
              ·
                refine ⟨2082779774340031100723671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11108158796480165870526245 2082779774340031100723671)
                ·
                  refine ⟨3124169661510046651085507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2082779774340031100723671 3124169661510046651085507)
                  ·
                    refine ⟨4686254492265069976628261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3124169661510046651085507 4686254492265069976628261)
                    ·
                      refine ⟨878672717299700620617799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4686254492265069976628261 878672717299700620617799)
                      ·
                        rfl

theorem cell23_1711209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_1711209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711209 prefixEnd_1711209 := by exact prefixLift 1711209
  have htrace : WordTrace (prefixWord ++ tailWord_1711209) baseStart_1711209 baseEnd_1711209 := by
    simpa [prefixWord, tailWord_1711209, baseEnd_1711209] using wordTrace_append hprefix tailTrace_1711209
  have hstable : (prefixWord ++ tailWord_1711209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711209).length < 2 ^ (prefixWord ++ tailWord_1711209).sum := by decide
  have hdescent : baseEnd_1711209 < baseStart_1711209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711212 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_1711212 : Nat := 118140960795 + 1711212 * 2 ^ 59
def prefixEnd_1711212 : Nat := 4983230072969 + 3 ^ 40 * 1711212 * 2
def baseEnd_1711212 : Nat := 878674257741664108880285

theorem tailTrace_1711212 : CollatzResearch.WordTrace tailWord_1711212 prefixEnd_1711212 878674257741664108880285 := by
  unfold tailWord_1711212
  simp only [CollatzResearch.WordTrace]
  refine ⟨31206514538289325293679945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41608686051052433724906593 31206514538289325293679945)
  ·
    refine ⟨23404885903716993970259959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31206514538289325293679945 23404885903716993970259959)
    ·
      refine ⟨35107328855575490955389939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23404885903716993970259959 35107328855575490955389939)
      ·
        refine ⟨52660993283363236433084909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35107328855575490955389939 52660993283363236433084909)
        ·
          refine ⟨19747872481261213662406841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52660993283363236433084909 19747872481261213662406841)
          ·
            refine ⟨14810904360945910246805131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19747872481261213662406841 14810904360945910246805131)
            ·
              refine ⟨22216356541418865370207697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14810904360945910246805131 22216356541418865370207697)
              ·
                refine ⟨16662267406064149027655773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22216356541418865370207697 16662267406064149027655773)
                ·
                  refine ⟨6248350277274055885370915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16662267406064149027655773 6248350277274055885370915)
                  ·
                    refine ⟨9372525415911083828056373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248350277274055885370915 9372525415911083828056373)
                    ·
                      refine ⟨878674257741664108880285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9372525415911083828056373 878674257741664108880285)
                      ·
                        rfl

theorem cell23_1711212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_1711212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711212 prefixEnd_1711212 := by exact prefixLift 1711212
  have htrace : WordTrace (prefixWord ++ tailWord_1711212) baseStart_1711212 baseEnd_1711212 := by
    simpa [prefixWord, tailWord_1711212, baseEnd_1711212] using wordTrace_append hprefix tailTrace_1711212
  have hstable : (prefixWord ++ tailWord_1711212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711212).length < 2 ^ (prefixWord ++ tailWord_1711212).sum := by decide
  have hdescent : baseEnd_1711212 < baseStart_1711212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711229 : List Nat := [1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_1711229 : Nat := 118140960795 + 1711229 * 2 ^ 59
def prefixEnd_1711229 : Nat := 4983230072969 + 3 ^ 40 * 1711229 * 2
def baseEnd_1711229 : Nat := 878682986912790542367707

theorem tailTrace_1711229 : CollatzResearch.WordTrace tailWord_1711229 prefixEnd_1711229 878682986912790542367707 := by
  unfold tailWord_1711229
  simp only [CollatzResearch.WordTrace]
  refine ⟨62413649117517062490728741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41609099411678041660485827 62413649117517062490728741)
  ·
    refine ⟨11702559209534449217011639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62413649117517062490728741 11702559209534449217011639)
    ·
      refine ⟨17553838814301673825517459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11702559209534449217011639 17553838814301673825517459)
      ·
        refine ⟨26330758221452510738276189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17553838814301673825517459 26330758221452510738276189)
        ·
          refine ⟨9874034333044691526853571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26330758221452510738276189 9874034333044691526853571)
          ·
            refine ⟨14811051499567037290280357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9874034333044691526853571 14811051499567037290280357)
            ·
              refine ⟨2777072156168819491927567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14811051499567037290280357 2777072156168819491927567)
              ·
                refine ⟨4165608234253229237891351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777072156168819491927567 4165608234253229237891351)
                ·
                  refine ⟨6248412351379843856837027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4165608234253229237891351 6248412351379843856837027)
                  ·
                    refine ⟨9372618527069765785255541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6248412351379843856837027 9372618527069765785255541)
                    ·
                      refine ⟨878682986912790542367707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9372618527069765785255541 878682986912790542367707)
                      ·
                        rfl

theorem cell23_1711229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_1711229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711229 prefixEnd_1711229 := by exact prefixLift 1711229
  have htrace : WordTrace (prefixWord ++ tailWord_1711229) baseStart_1711229 baseEnd_1711229 := by
    simpa [prefixWord, tailWord_1711229, baseEnd_1711229] using wordTrace_append hprefix tailTrace_1711229
  have hstable : (prefixWord ++ tailWord_1711229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711229).length < 2 ^ (prefixWord ++ tailWord_1711229).sum := by decide
  have hdescent : baseEnd_1711229 < baseStart_1711229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711243 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 1, 2, 2]
def baseStart_1711243 : Nat := 118140960795 + 1711243 * 2 ^ 59
def prefixEnd_1711243 : Nat := 4983230072969 + 3 ^ 40 * 1711243 * 2
def baseEnd_1711243 : Nat := 878690175641953487592643

theorem tailTrace_1711243 : CollatzResearch.WordTrace tailWord_1711243 prefixEnd_1711243 878690175641953487592643 := by
  unfold tailWord_1711243
  simp only [CollatzResearch.WordTrace]
  refine ⟨62414159739466342881738383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41609439826310895254492255 62414159739466342881738383)
  ·
    refine ⟨93621239609199514322607575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62414159739466342881738383 93621239609199514322607575)
    ·
      refine ⟨140431859413799271483911363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93621239609199514322607575 140431859413799271483911363)
      ·
        refine ⟨210647789120698907225867045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140431859413799271483911363 210647789120698907225867045)
        ·
          refine ⟨39496460460131045104850071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210647789120698907225867045 39496460460131045104850071)
          ·
            refine ⟨59244690690196567657275107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39496460460131045104850071 59244690690196567657275107)
            ·
              refine ⟨88867036035294851485912661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59244690690196567657275107 88867036035294851485912661)
              ·
                refine ⟨1041410578538611540850539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 88867036035294851485912661 1041410578538611540850539)
                ·
                  refine ⟨1562115867807917311275809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041410578538611540850539 1562115867807917311275809)
                  ·
                    refine ⟨1171586900855937983456857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562115867807917311275809 1171586900855937983456857)
                    ·
                      refine ⟨878690175641953487592643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171586900855937983456857 878690175641953487592643)
                      ·
                        rfl

theorem cell23_1711243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 1, 2, 2].length) (baseStart_1711243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711243 prefixEnd_1711243 := by exact prefixLift 1711243
  have htrace : WordTrace (prefixWord ++ tailWord_1711243) baseStart_1711243 baseEnd_1711243 := by
    simpa [prefixWord, tailWord_1711243, baseEnd_1711243] using wordTrace_append hprefix tailTrace_1711243
  have hstable : (prefixWord ++ tailWord_1711243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711243).length < 2 ^ (prefixWord ++ tailWord_1711243).sum := by decide
  have hdescent : baseEnd_1711243 < baseStart_1711243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711259 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 3]
def baseStart_1711259 : Nat := 118140960795 + 1711259 * 2 ^ 59
def prefixEnd_1711259 : Nat := 4983230072969 + 3 ^ 40 * 1711259 * 2
def baseEnd_1711259 : Nat := 878698391332425424992569

theorem tailTrace_1711259 : CollatzResearch.WordTrace tailWord_1711259 prefixEnd_1711259 878698391332425424992569 := by
  unfold tailWord_1711259
  simp only [CollatzResearch.WordTrace]
  refine ⟨62414743307408377614320831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41609828871605585076213887 62414743307408377614320831)
  ·
    refine ⟨93622114961112566421481247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62414743307408377614320831 93622114961112566421481247)
    ·
      refine ⟨140433172441668849632221871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93622114961112566421481247 140433172441668849632221871)
      ·
        refine ⟨210649758662503274448332807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140433172441668849632221871 210649758662503274448332807)
        ·
          refine ⟨315974637993754911672499211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210649758662503274448332807 315974637993754911672499211)
          ·
            refine ⟨473961956990632367508748817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315974637993754911672499211 473961956990632367508748817)
            ·
              refine ⟨355471467742974275631561613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473961956990632367508748817 355471467742974275631561613)
              ·
                refine ⟨133301800403615353361835605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 355471467742974275631561613 133301800403615353361835605)
                ·
                  refine ⟨1562130473479867422209011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 133301800403615353361835605 1562130473479867422209011)
                  ·
                    refine ⟨2343195710219801133313517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562130473479867422209011 2343195710219801133313517)
                    ·
                      refine ⟨878698391332425424992569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2343195710219801133313517 878698391332425424992569)
                      ·
                        rfl

theorem cell23_1711259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 1, 3].length) (baseStart_1711259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711259 prefixEnd_1711259 := by exact prefixLift 1711259
  have htrace : WordTrace (prefixWord ++ tailWord_1711259) baseStart_1711259 baseEnd_1711259 := by
    simpa [prefixWord, tailWord_1711259, baseEnd_1711259] using wordTrace_append hprefix tailTrace_1711259
  have hstable : (prefixWord ++ tailWord_1711259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711259).length < 2 ^ (prefixWord ++ tailWord_1711259).sum := by decide
  have hdescent : baseEnd_1711259 < baseStart_1711259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711294 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2]
def baseStart_1711294 : Nat := 118140960795 + 1711294 * 2 ^ 59
def prefixEnd_1711294 : Nat := 4983230072969 + 3 ^ 40 * 1711294 * 2
def baseEnd_1711294 : Nat := 878716363155332788054909

theorem tailTrace_1711294 : CollatzResearch.WordTrace tailWord_1711294 prefixEnd_1711294 878716363155332788054909 := by
  unfold tailWord_1711294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802002482785197323980617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41610679908187719061229957 7802002482785197323980617)
  ·
    refine ⟨5851501862088897992985463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7802002482785197323980617 5851501862088897992985463)
    ·
      refine ⟨8777252793133346989478195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5851501862088897992985463 8777252793133346989478195)
      ·
        refine ⟨13165879189700020484217293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777252793133346989478195 13165879189700020484217293)
        ·
          refine ⟨4937204696137507681581485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13165879189700020484217293 4937204696137507681581485)
          ·
            refine ⟨1851451761051565380593057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4937204696137507681581485 1851451761051565380593057)
            ·
              refine ⟨1388588820788674035444793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851451761051565380593057 1388588820788674035444793)
              ·
                refine ⟨1041441615591505526583595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388588820788674035444793 1041441615591505526583595)
                ·
                  refine ⟨1562162423387258289875393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041441615591505526583595 1562162423387258289875393)
                  ·
                    refine ⟨1171621817540443717406545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562162423387258289875393 1171621817540443717406545)
                    ·
                      refine ⟨878716363155332788054909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171621817540443717406545 878716363155332788054909)
                      ·
                        rfl

theorem cell23_1711294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_1711294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711294 prefixEnd_1711294 := by exact prefixLift 1711294
  have htrace : WordTrace (prefixWord ++ tailWord_1711294) baseStart_1711294 baseEnd_1711294 := by
    simpa [prefixWord, tailWord_1711294, baseEnd_1711294] using wordTrace_append hprefix tailTrace_1711294
  have hstable : (prefixWord ++ tailWord_1711294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711294).length < 2 ^ (prefixWord ++ tailWord_1711294).sum := by decide
  have hdescent : baseEnd_1711294 < baseStart_1711294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711356 : List Nat := [2, 2, 2, 1, 5, 1, 2, 1, 7]
def baseStart_1711356 : Nat := 118140960795 + 1711356 * 2 ^ 59
def prefixEnd_1711356 : Nat := 4983230072969 + 3 ^ 40 * 1711356 * 2
def baseEnd_1711356 : Nat := 97638688772879060608847

theorem tailTrace_1711356 : CollatzResearch.WordTrace tailWord_1711356 prefixEnd_1711356 97638688772879060608847 := by
  unfold tailWord_1711356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31209140594028481590300961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41612187458704642120401281 31209140594028481590300961)
  ·
    refine ⟨23406855445521361192725721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31209140594028481590300961 23406855445521361192725721)
    ·
      refine ⟨17555141584141020894544291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23406855445521361192725721 17555141584141020894544291)
      ·
        refine ⟨26332712376211531341816437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17555141584141020894544291 26332712376211531341816437)
        ·
          refine ⟨2468691785269831063295291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26332712376211531341816437 2468691785269831063295291)
          ·
            refine ⟨3703037677904746594942937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468691785269831063295291 3703037677904746594942937)
            ·
              refine ⟨2777278258428559946207203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703037677904746594942937 2777278258428559946207203)
              ·
                refine ⟨4165917387642839919310805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2777278258428559946207203 4165917387642839919310805)
                ·
                  refine ⟨97638688772879060608847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4165917387642839919310805 97638688772879060608847)
                  ·
                    rfl

theorem cell23_1711356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_1711356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711356 prefixEnd_1711356 := by exact prefixLift 1711356
  have htrace : WordTrace (prefixWord ++ tailWord_1711356) baseStart_1711356 baseEnd_1711356 := by
    simpa [prefixWord, tailWord_1711356, baseEnd_1711356] using wordTrace_append hprefix tailTrace_1711356
  have hstable : (prefixWord ++ tailWord_1711356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711356).length < 2 ^ (prefixWord ++ tailWord_1711356).sum := by decide
  have hdescent : baseEnd_1711356 < baseStart_1711356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711463 : List Nat := [1, 1, 5, 1, 4, 1, 2, 2, 6]
def baseStart_1711463 : Nat := 118140960795 + 1711463 * 2 ^ 59
def prefixEnd_1711463 : Nat := 4983230072969 + 3 ^ 40 * 1711463 * 2
def baseEnd_1711463 : Nat := 97644793487326958537959

theorem tailTrace_1711463 : CollatzResearch.WordTrace tailWord_1711463 prefixEnd_1711463 97644793487326958537959 := by
  unfold tailWord_1711463
  simp only [CollatzResearch.WordTrace]
  refine ⟨62422183798669320454747043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41614789199112880303164695 62422183798669320454747043)
  ·
    refine ⟨93633275698003980682120565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62422183798669320454747043 93633275698003980682120565)
    ·
      refine ⟨8778119596687873188948803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93633275698003980682120565 8778119596687873188948803)
      ·
        refine ⟨13167179395031809783423205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8778119596687873188948803 13167179395031809783423205)
        ·
          refine ⟨2468846136568464334391851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13167179395031809783423205 2468846136568464334391851)
          ·
            refine ⟨3703269204852696501587777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2468846136568464334391851 3703269204852696501587777)
            ·
              refine ⟨2777451903639522376190833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703269204852696501587777 2777451903639522376190833)
              ·
                refine ⟨2083088927729641782143125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777451903639522376190833 2083088927729641782143125)
                ·
                  refine ⟨97644793487326958537959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2083088927729641782143125 97644793487326958537959)
                  ·
                    rfl

theorem cell23_1711463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 2, 6].length) (baseStart_1711463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711463 prefixEnd_1711463 := by exact prefixLift 1711463
  have htrace : WordTrace (prefixWord ++ tailWord_1711463) baseStart_1711463 baseEnd_1711463 := by
    simpa [prefixWord, tailWord_1711463, baseEnd_1711463] using wordTrace_append hprefix tailTrace_1711463
  have hstable : (prefixWord ++ tailWord_1711463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711463).length < 2 ^ (prefixWord ++ tailWord_1711463).sum := by decide
  have hdescent : baseEnd_1711463 < baseStart_1711463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711513 : List Nat := [1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_1711513 : Nat := 118140960795 + 1711513 * 2 ^ 59
def prefixEnd_1711513 : Nat := 4983230072969 + 3 ^ 40 * 1711513 * 2
def baseEnd_1711513 : Nat := 878828815418667431216401

theorem tailTrace_1711513 : CollatzResearch.WordTrace tailWord_1711513 prefixEnd_1711513 878828815418667431216401 := by
  unfold tailWord_1711513
  simp only [CollatzResearch.WordTrace]
  refine ⟨62424007448488178994067193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41616004965658785996044795 62424007448488178994067193)
  ·
    refine ⟨46818005586366134245550395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62424007448488178994067193 46818005586366134245550395)
    ·
      refine ⟨70227008379549201368325593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818005586366134245550395 70227008379549201368325593)
      ·
        refine ⟨52670256284661901026244195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70227008379549201368325593 52670256284661901026244195)
        ·
          refine ⟨79005384426992851539366293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52670256284661901026244195 79005384426992851539366293)
          ·
            refine ⟨3703377395015289915907795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 79005384426992851539366293 3703377395015289915907795)
            ·
              refine ⟨5555066092522934873861693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703377395015289915907795 5555066092522934873861693)
              ·
                refine ⟨2083149784696100577698135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5555066092522934873861693 2083149784696100577698135)
                ·
                  refine ⟨3124724677044150866547203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083149784696100577698135 3124724677044150866547203)
                  ·
                    refine ⟨4687087015566226299820805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3124724677044150866547203 4687087015566226299820805)
                    ·
                      refine ⟨878828815418667431216401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4687087015566226299820805 878828815418667431216401)
                      ·
                        rfl

theorem cell23_1711513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_1711513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711513 prefixEnd_1711513 := by exact prefixLift 1711513
  have htrace : WordTrace (prefixWord ++ tailWord_1711513) baseStart_1711513 baseEnd_1711513 := by
    simpa [prefixWord, tailWord_1711513, baseEnd_1711513] using wordTrace_append hprefix tailTrace_1711513
  have hstable : (prefixWord ++ tailWord_1711513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711513).length < 2 ^ (prefixWord ++ tailWord_1711513).sum := by decide
  have hdescent : baseEnd_1711513 < baseStart_1711513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711529 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1711529 : Nat := 118140960795 + 1711529 * 2 ^ 59
def prefixEnd_1711529 : Nat := 4983230072969 + 3 ^ 40 * 1711529 * 2
def baseEnd_1711529 : Nat := 878837031109139368616327

theorem tailTrace_1711529 : CollatzResearch.WordTrace tailWord_1711529 prefixEnd_1711529 878837031109139368616327 := by
  unfold tailWord_1711529
  simp only [CollatzResearch.WordTrace]
  refine ⟨62424591016430213726649641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41616394010953475817766427 62424591016430213726649641)
  ·
    refine ⟨46818443262322660294987231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62424591016430213726649641 46818443262322660294987231)
    ·
      refine ⟨70227664893483990442480847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46818443262322660294987231 70227664893483990442480847)
      ·
        refine ⟨105341497340225985663721271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70227664893483990442480847 105341497340225985663721271)
        ·
          refine ⟨158012246010338978495581907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105341497340225985663721271 158012246010338978495581907)
          ·
            refine ⟨237018369015508467743372861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158012246010338978495581907 237018369015508467743372861)
            ·
              refine ⟨88881888380815675403764823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237018369015508467743372861 88881888380815675403764823)
              ·
                refine ⟨133322832571223513105647235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88881888380815675403764823 133322832571223513105647235)
                ·
                  refine ⟨199984248856835269658470853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133322832571223513105647235 199984248856835269658470853)
                  ·
                    refine ⟨37497046660656613060963285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199984248856835269658470853 37497046660656613060963285)
                    ·
                      refine ⟨878837031109139368616327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37497046660656613060963285 878837031109139368616327)
                      ·
                        rfl

theorem cell23_1711529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1711529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711529 prefixEnd_1711529 := by exact prefixLift 1711529
  have htrace : WordTrace (prefixWord ++ tailWord_1711529) baseStart_1711529 baseEnd_1711529 := by
    simpa [prefixWord, tailWord_1711529, baseEnd_1711529] using wordTrace_append hprefix tailTrace_1711529
  have hstable : (prefixWord ++ tailWord_1711529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711529).length < 2 ^ (prefixWord ++ tailWord_1711529).sum := by decide
  have hdescent : baseEnd_1711529 < baseStart_1711529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711533 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_1711533 : Nat := 118140960795 + 1711533 * 2 ^ 59
def prefixEnd_1711533 : Nat := 4983230072969 + 3 ^ 40 * 1711533 * 2
def baseEnd_1711533 : Nat := 878839085031757352966309

theorem tailTrace_1711533 : CollatzResearch.WordTrace tailWord_1711533 prefixEnd_1711533 878839085031757352966309 := by
  unfold tailWord_1711533
  simp only [CollatzResearch.WordTrace]
  refine ⟨62424736908415722409795253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41616491272277148273196835 62424736908415722409795253)
  ·
    refine ⟨5852319085163973975918305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62424736908415722409795253 5852319085163973975918305)
    ·
      refine ⟨4389239313872980481938729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5852319085163973975918305 4389239313872980481938729)
      ·
        refine ⟨3291929485404735361454047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389239313872980481938729 3291929485404735361454047)
        ·
          refine ⟨4937894228107103042181071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3291929485404735361454047 4937894228107103042181071)
          ·
            refine ⟨7406841342160654563271607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937894228107103042181071 7406841342160654563271607)
            ·
              refine ⟨11110262013240981844907411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7406841342160654563271607 11110262013240981844907411)
              ·
                refine ⟨16665393019861472767361117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11110262013240981844907411 16665393019861472767361117)
                ·
                  refine ⟨6249522382448052287760419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16665393019861472767361117 6249522382448052287760419)
                  ·
                    refine ⟨9374283573672078431640629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6249522382448052287760419 9374283573672078431640629)
                    ·
                      refine ⟨878839085031757352966309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9374283573672078431640629 878839085031757352966309)
                      ·
                        rfl

theorem cell23_1711533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_1711533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711533 prefixEnd_1711533 := by exact prefixLift 1711533
  have htrace : WordTrace (prefixWord ++ tailWord_1711533) baseStart_1711533 baseEnd_1711533 := by
    simpa [prefixWord, tailWord_1711533, baseEnd_1711533] using wordTrace_append hprefix tailTrace_1711533
  have hstable : (prefixWord ++ tailWord_1711533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711533).length < 2 ^ (prefixWord ++ tailWord_1711533).sum := by decide
  have hdescent : baseEnd_1711533 < baseStart_1711533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711563 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 3]
def baseStart_1711563 : Nat := 118140960795 + 1711563 * 2 ^ 59
def prefixEnd_1711563 : Nat := 4983230072969 + 3 ^ 40 * 1711563 * 2
def baseEnd_1711563 : Nat := 878854489451392235591171

theorem tailTrace_1711563 : CollatzResearch.WordTrace tailWord_1711563 prefixEnd_1711563 878854489451392235591171 := by
  unfold tailWord_1711563
  simp only [CollatzResearch.WordTrace]
  refine ⟨62425831098307037533387343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41617220732204691688924895 62425831098307037533387343)
  ·
    refine ⟨93638746647460556300081015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62425831098307037533387343 93638746647460556300081015)
    ·
      refine ⟨140458119971190834450121523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93638746647460556300081015 140458119971190834450121523)
      ·
        refine ⟨210687179956786251675182285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140458119971190834450121523 210687179956786251675182285)
        ·
          refine ⟨79007692483794844378193357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210687179956786251675182285 79007692483794844378193357)
          ·
            refine ⟨29627884681423066641822509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79007692483794844378193357 29627884681423066641822509)
            ·
              refine ⟨11110456755533649990683441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29627884681423066641822509 11110456755533649990683441)
              ·
                refine ⟨8332842566650237493012581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11110456755533649990683441 8332842566650237493012581)
                ·
                  refine ⟨1562407981246919529939859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8332842566650237493012581 1562407981246919529939859)
                  ·
                    refine ⟨2343611971870379294909789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562407981246919529939859 2343611971870379294909789)
                    ·
                      refine ⟨878854489451392235591171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2343611971870379294909789 878854489451392235591171)
                      ·
                        rfl

theorem cell23_1711563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 1, 3].length) (baseStart_1711563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711563 prefixEnd_1711563 := by exact prefixLift 1711563
  have htrace : WordTrace (prefixWord ++ tailWord_1711563) baseStart_1711563 baseEnd_1711563 := by
    simpa [prefixWord, tailWord_1711563, baseEnd_1711563] using wordTrace_append hprefix tailTrace_1711563
  have hstable : (prefixWord ++ tailWord_1711563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711563).length < 2 ^ (prefixWord ++ tailWord_1711563).sum := by decide
  have hdescent : baseEnd_1711563 < baseStart_1711563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711564 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 1, 2, 2]
def baseStart_1711564 : Nat := 118140960795 + 1711564 * 2 ^ 59
def prefixEnd_1711564 : Nat := 4983230072969 + 3 ^ 40 * 1711564 * 2
def baseEnd_1711564 : Nat := 878855002932046731678667

theorem tailTrace_1711564 : CollatzResearch.WordTrace tailWord_1711564 prefixEnd_1711564 878855002932046731678667 := by
  unfold tailWord_1711564
  simp only [CollatzResearch.WordTrace]
  refine ⟨31212933785651707352086873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41617245047535609802782497 31212933785651707352086873)
  ·
    refine ⟨23409700339238780514065155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31212933785651707352086873 23409700339238780514065155)
    ·
      refine ⟨35114550508858170771097733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23409700339238780514065155 35114550508858170771097733)
      ·
        refine ⟨6583978220410907019580825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35114550508858170771097733 6583978220410907019580825)
        ·
          refine ⟨4937983665308180264685619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6583978220410907019580825 4937983665308180264685619)
          ·
            refine ⟨7406975497962270397028429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4937983665308180264685619 7406975497962270397028429)
            ·
              refine ⟨2777615811735851398885661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7406975497962270397028429 2777615811735851398885661)
              ·
                refine ⟨1041605929400944274582123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2777615811735851398885661 1041605929400944274582123)
                ·
                  refine ⟨1562408894101416411873185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041605929400944274582123 1562408894101416411873185)
                  ·
                    refine ⟨1171806670576062308904889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562408894101416411873185 1171806670576062308904889)
                    ·
                      refine ⟨878855002932046731678667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171806670576062308904889 878855002932046731678667)
                      ·
                        rfl

theorem cell23_1711564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_1711564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711564 prefixEnd_1711564 := by exact prefixLift 1711564
  have htrace : WordTrace (prefixWord ++ tailWord_1711564) baseStart_1711564 baseEnd_1711564 := by
    simpa [prefixWord, tailWord_1711564, baseEnd_1711564] using wordTrace_append hprefix tailTrace_1711564
  have hstable : (prefixWord ++ tailWord_1711564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711564).length < 2 ^ (prefixWord ++ tailWord_1711564).sum := by decide
  have hdescent : baseEnd_1711564 < baseStart_1711564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711581 : List Nat := [1, 4, 3, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_1711581 : Nat := 118140960795 + 1711581 * 2 ^ 59
def prefixEnd_1711581 : Nat := 4983230072969 + 3 ^ 40 * 1711581 * 2
def baseEnd_1711581 : Nat := 878863732103173165166089

theorem tailTrace_1711581 : CollatzResearch.WordTrace tailWord_1711581 prefixEnd_1711581 878863732103173165166089 := by
  unfold tailWord_1711581
  simp only [CollatzResearch.WordTrace]
  refine ⟨62426487612241826607542597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41617658408161217738361731 62426487612241826607542597)
  ·
    refine ⟨11704966427295342488914237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62426487612241826607542597 11704966427295342488914237)
    ·
      refine ⟨4389362410235753433342839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11704966427295342488914237 4389362410235753433342839)
      ·
        refine ⟨6584043615353630150014259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389362410235753433342839 6584043615353630150014259)
        ·
          refine ⟨9876065423030445225021389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584043615353630150014259 9876065423030445225021389)
          ·
            refine ⟨3703524533636416959383021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9876065423030445225021389 3703524533636416959383021)
            ·
              refine ⟨1388821700113656359768633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3703524533636416959383021 1388821700113656359768633)
              ·
                refine ⟨1041616275085242269826475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388821700113656359768633 1041616275085242269826475)
                ·
                  refine ⟨1562424412627863404739713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041616275085242269826475 1562424412627863404739713)
                  ·
                    refine ⟨1171818309470897553554785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562424412627863404739713 1171818309470897553554785)
                    ·
                      refine ⟨878863732103173165166089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171818309470897553554785 878863732103173165166089)
                      ·
                        rfl

theorem cell23_1711581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_1711581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711581 prefixEnd_1711581 := by exact prefixLift 1711581
  have htrace : WordTrace (prefixWord ++ tailWord_1711581) baseStart_1711581 baseEnd_1711581 := by
    simpa [prefixWord, tailWord_1711581, baseEnd_1711581] using wordTrace_append hprefix tailTrace_1711581
  have hstable : (prefixWord ++ tailWord_1711581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711581).length < 2 ^ (prefixWord ++ tailWord_1711581).sum := by decide
  have hdescent : baseEnd_1711581 < baseStart_1711581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711623 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1711623 : Nat := 118140960795 + 1711623 * 2 ^ 59
def prefixEnd_1711623 : Nat := 4983230072969 + 3 ^ 40 * 1711623 * 2
def baseEnd_1711623 : Nat := 878885298290662000840895

theorem tailTrace_1711623 : CollatzResearch.WordTrace tailWord_1711623 prefixEnd_1711623 878885298290662000840895 := by
  unfold tailWord_1711623
  simp only [CollatzResearch.WordTrace]
  refine ⟨62428019478089667780571523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41618679652059778520381015 62428019478089667780571523)
  ·
    refine ⟨93642029217134501670857285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62428019478089667780571523 93642029217134501670857285)
    ·
      refine ⟨17557880478212719063285741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93642029217134501670857285 17557880478212719063285741)
      ·
        refine ⟨6584205179329769648732153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17557880478212719063285741 6584205179329769648732153)
        ·
          refine ⟨4938153884497327236549115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6584205179329769648732153 4938153884497327236549115)
          ·
            refine ⟨7407230826745990854823673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938153884497327236549115 7407230826745990854823673)
            ·
              refine ⟨5555423120059493141117755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7407230826745990854823673 5555423120059493141117755)
              ·
                refine ⟨8333134680089239711676633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555423120059493141117755 8333134680089239711676633)
                ·
                  refine ⟨6249851010066929783757475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8333134680089239711676633 6249851010066929783757475)
                  ·
                    refine ⟨9374776515100394675636213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6249851010066929783757475 9374776515100394675636213)
                    ·
                      refine ⟨878885298290662000840895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9374776515100394675636213 878885298290662000840895)
                      ·
                        rfl

theorem cell23_1711623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1711623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711623 prefixEnd_1711623 := by exact prefixLift 1711623
  have htrace : WordTrace (prefixWord ++ tailWord_1711623) baseStart_1711623 baseEnd_1711623 := by
    simpa [prefixWord, tailWord_1711623, baseEnd_1711623] using wordTrace_append hprefix tailTrace_1711623
  have hstable : (prefixWord ++ tailWord_1711623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711623).length < 2 ^ (prefixWord ++ tailWord_1711623).sum := by decide
  have hdescent : baseEnd_1711623 < baseStart_1711623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711637 : List Nat := [1, 3, 2, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_1711637 : Nat := 118140960795 + 1711637 * 2 ^ 59
def prefixEnd_1711637 : Nat := 4983230072969 + 3 ^ 40 * 1711637 * 2
def baseEnd_1711637 : Nat := 878892487019824946065831

theorem tailTrace_1711637 : CollatzResearch.WordTrace tailWord_1711637 prefixEnd_1711637 878892487019824946065831 := by
  unfold tailWord_1711637
  simp only [CollatzResearch.WordTrace]
  refine ⟨62428530100038948171581165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41619020066692632114387443 62428530100038948171581165)
  ·
    refine ⟨23410698787514605564342937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62428530100038948171581165 23410698787514605564342937)
    ·
      refine ⟨17558024090635954173257203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23410698787514605564342937 17558024090635954173257203)
      ·
        refine ⟨26337036135953931259885805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17558024090635954173257203 26337036135953931259885805)
        ·
          refine ⟨9876388550982724222457177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26337036135953931259885805 9876388550982724222457177)
          ·
            refine ⟨7407291413237043166842883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9876388550982724222457177 7407291413237043166842883)
            ·
              refine ⟨11110937119855564750264325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7407291413237043166842883 11110937119855564750264325)
              ·
                refine ⟨2083300709972918390674561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11110937119855564750264325 2083300709972918390674561)
                ·
                  refine ⟨1562475532479688793005921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2083300709972918390674561 1562475532479688793005921)
                  ·
                    refine ⟨1171856649359766594754441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562475532479688793005921 1171856649359766594754441)
                    ·
                      refine ⟨878892487019824946065831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171856649359766594754441 878892487019824946065831)
                      ·
                        rfl

theorem cell23_1711637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_1711637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711637 prefixEnd_1711637 := by exact prefixLift 1711637
  have htrace : WordTrace (prefixWord ++ tailWord_1711637) baseStart_1711637 baseEnd_1711637 := by
    simpa [prefixWord, tailWord_1711637, baseEnd_1711637] using wordTrace_append hprefix tailTrace_1711637
  have hstable : (prefixWord ++ tailWord_1711637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711637).length < 2 ^ (prefixWord ++ tailWord_1711637).sum := by decide
  have hdescent : baseEnd_1711637 < baseStart_1711637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711673 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 7]
def baseStart_1711673 : Nat := 118140960795 + 1711673 * 2 ^ 59
def prefixEnd_1711673 : Nat := 4983230072969 + 3 ^ 40 * 1711673 * 2
def baseEnd_1711673 : Nat := 292970324107795601738555

theorem tailTrace_1711673 : CollatzResearch.WordTrace tailWord_1711673 prefixEnd_1711673 292970324107795601738555 := by
  unfold tailWord_1711673
  simp only [CollatzResearch.WordTrace]
  refine ⟨62429843127908526319891673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41619895418605684213261115 62429843127908526319891673)
  ·
    refine ⟨46822382345931394739918755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62429843127908526319891673 46822382345931394739918755)
    ·
      refine ⟨70233573518897092109878133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46822382345931394739918755 70233573518897092109878133)
      ·
        refine ⟨6584397517396602385301075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70233573518897092109878133 6584397517396602385301075)
        ·
          refine ⟨9876596276094903577951613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6584397517396602385301075 9876596276094903577951613)
          ·
            refine ⟨3703723603535588841731855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9876596276094903577951613 3703723603535588841731855)
            ·
              refine ⟨5555585405303383262597783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703723603535588841731855 5555585405303383262597783)
              ·
                refine ⟨8333378107955074893896675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555585405303383262597783 8333378107955074893896675)
                ·
                  refine ⟨12500067161932612340845013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333378107955074893896675 12500067161932612340845013)
                  ·
                    refine ⟨292970324107795601738555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12500067161932612340845013 292970324107795601738555)
                    ·
                      rfl

theorem cell23_1711673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_1711673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711673 prefixEnd_1711673 := by exact prefixLift 1711673
  have htrace : WordTrace (prefixWord ++ tailWord_1711673) baseStart_1711673 baseEnd_1711673 := by
    simpa [prefixWord, tailWord_1711673, baseEnd_1711673] using wordTrace_append hprefix tailTrace_1711673
  have hstable : (prefixWord ++ tailWord_1711673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711673).length < 2 ^ (prefixWord ++ tailWord_1711673).sum := by decide
  have hdescent : baseEnd_1711673 < baseStart_1711673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711677 : List Nat := [1, 4, 1, 3, 3, 1, 2, 3, 5]
def baseStart_1711677 : Nat := 118140960795 + 1711677 * 2 ^ 59
def prefixEnd_1711677 : Nat := 4983230072969 + 3 ^ 40 * 1711677 * 2
def baseEnd_1711677 : Nat := 97657002916222754396183

theorem tailTrace_1711677 : CollatzResearch.WordTrace tailWord_1711677 prefixEnd_1711677 97657002916222754396183 := by
  unfold tailWord_1711677
  simp only [CollatzResearch.WordTrace]
  refine ⟨62429989019894035003037285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41619992679929356668691523 62429989019894035003037285)
  ·
    refine ⟨11705622941230131563069491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62429989019894035003037285 11705622941230131563069491)
    ·
      refine ⟨17558434411845197344604237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11705622941230131563069491 17558434411845197344604237)
      ·
        refine ⟨6584412904441949004226589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17558434411845197344604237 6584412904441949004226589)
        ·
          refine ⟨2469154839165730876584971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6584412904441949004226589 2469154839165730876584971)
          ·
            refine ⟨3703732258748596314877457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469154839165730876584971 3703732258748596314877457)
            ·
              refine ⟨2777799194061447236158093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3703732258748596314877457 2777799194061447236158093)
              ·
                refine ⟨1041674697773042713559285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2777799194061447236158093 1041674697773042713559285)
                ·
                  refine ⟨97657002916222754396183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1041674697773042713559285 97657002916222754396183)
                  ·
                    rfl

theorem cell23_1711677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_1711677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711677 prefixEnd_1711677 := by exact prefixLift 1711677
  have htrace : WordTrace (prefixWord ++ tailWord_1711677) baseStart_1711677 baseEnd_1711677 := by
    simpa [prefixWord, tailWord_1711677, baseEnd_1711677] using wordTrace_append hprefix tailTrace_1711677
  have hstable : (prefixWord ++ tailWord_1711677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711677).length < 2 ^ (prefixWord ++ tailWord_1711677).sum := by decide
  have hdescent : baseEnd_1711677 < baseStart_1711677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711713 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1711713 : Nat := 118140960795 + 1711713 * 2 ^ 59
def prefixEnd_1711713 : Nat := 4983230072969 + 3 ^ 40 * 1711713 * 2
def baseEnd_1711713 : Nat := 878931511549566648715481

theorem tailTrace_1711713 : CollatzResearch.WordTrace tailWord_1711713 prefixEnd_1711713 878931511549566648715481 := by
  unfold tailWord_1711713
  simp only [CollatzResearch.WordTrace]
  refine ⟨62431302047763613151347793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41620868031842408767565195 62431302047763613151347793)
  ·
    refine ⟨46823476535822709863510845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62431302047763613151347793 46823476535822709863510845)
    ·
      refine ⟨17558803700933516198816567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46823476535822709863510845 17558803700933516198816567)
      ·
        refine ⟨26338205551400274298224851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17558803700933516198816567 26338205551400274298224851)
        ·
          refine ⟨39507308327100411447337277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26338205551400274298224851 39507308327100411447337277)
          ·
            refine ⟨14815240622662654292751479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39507308327100411447337277 14815240622662654292751479)
            ·
              refine ⟨22222860933993981439127219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14815240622662654292751479 22222860933993981439127219)
              ·
                refine ⟨33334291400990972158690829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22222860933993981439127219 33334291400990972158690829)
                ·
                  refine ⟨12500359275371614559509061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33334291400990972158690829 12500359275371614559509061)
                  ·
                    refine ⟨2343817364132177729907949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12500359275371614559509061 2343817364132177729907949)
                    ·
                      refine ⟨878931511549566648715481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2343817364132177729907949 878931511549566648715481)
                      ·
                        rfl

theorem cell23_1711713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1711713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711713 prefixEnd_1711713 := by exact prefixLift 1711713
  have htrace : WordTrace (prefixWord ++ tailWord_1711713) baseStart_1711713 baseEnd_1711713 := by
    simpa [prefixWord, tailWord_1711713, baseEnd_1711713] using wordTrace_append hprefix tailTrace_1711713
  have hstable : (prefixWord ++ tailWord_1711713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711713).length < 2 ^ (prefixWord ++ tailWord_1711713).sum := by decide
  have hdescent : baseEnd_1711713 < baseStart_1711713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711730 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1711730 : Nat := 118140960795 + 1711730 * 2 ^ 59
def prefixEnd_1711730 : Nat := 4983230072969 + 3 ^ 40 * 1711730 * 2
def baseEnd_1711730 : Nat := 878940240720693082202903

theorem tailTrace_1711730 : CollatzResearch.WordTrace tailWord_1711730 prefixEnd_1711730 878940240720693082202903 := by
  unfold tailWord_1711730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15607980522175506263679161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41621281392468016703144429 15607980522175506263679161)
  ·
    refine ⟨11705985391631629697759371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15607980522175506263679161 11705985391631629697759371)
    ·
      refine ⟨17558978087447444546639057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11705985391631629697759371 17558978087447444546639057)
      ·
        refine ⟨13169233565585583409979293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17558978087447444546639057 13169233565585583409979293)
        ·
          refine ⟨4938462587094593778742235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13169233565585583409979293 4938462587094593778742235)
          ·
            refine ⟨7407693880641890668113353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938462587094593778742235 7407693880641890668113353)
            ·
              refine ⟨5555770410481418001085015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7407693880641890668113353 5555770410481418001085015)
              ·
                refine ⟨8333655615722127001627523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555770410481418001085015 8333655615722127001627523)
                ·
                  refine ⟨12500483423583190502441285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8333655615722127001627523 12500483423583190502441285)
                  ·
                    refine ⟨2343840641921848219207741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12500483423583190502441285 2343840641921848219207741)
                    ·
                      refine ⟨878940240720693082202903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2343840641921848219207741 878940240720693082202903)
                      ·
                        rfl

theorem cell23_1711730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1711730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711730 prefixEnd_1711730 := by exact prefixLift 1711730
  have htrace : WordTrace (prefixWord ++ tailWord_1711730) baseStart_1711730 baseEnd_1711730 := by
    simpa [prefixWord, tailWord_1711730, baseEnd_1711730] using wordTrace_append hprefix tailTrace_1711730
  have hstable : (prefixWord ++ tailWord_1711730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711730).length < 2 ^ (prefixWord ++ tailWord_1711730).sum := by decide
  have hdescent : baseEnd_1711730 < baseStart_1711730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711767 : List Nat := [1, 1, 3, 3, 2, 4, 2, 1, 6]
def baseStart_1711767 : Nat := 118140960795 + 1711767 * 2 ^ 59
def prefixEnd_1711767 : Nat := 4983230072969 + 3 ^ 40 * 1711767 * 2
def baseEnd_1711767 : Nat := 97662137722767715271137

theorem tailTrace_1711767 : CollatzResearch.WordTrace tailWord_1711767 prefixEnd_1711767 97662137722767715271137 := by
  unfold tailWord_1711767
  simp only [CollatzResearch.WordTrace]
  refine ⟨62433271589567980373813555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41622181059711986915875703 62433271589567980373813555)
  ·
    refine ⟨93649907384351970560720333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62433271589567980373813555 93649907384351970560720333)
    ·
      refine ⟨35118715269131988960270125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93649907384351970560720333 35118715269131988960270125)
      ·
        refine ⟨13169518225924495860101297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35118715269131988960270125 13169518225924495860101297)
        ·
          refine ⟨9877138669443371895075973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13169518225924495860101297 9877138669443371895075973)
          ·
            refine ⟨1851963500520632230326745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9877138669443371895075973 1851963500520632230326745)
            ·
              refine ⟨1388972625390474172745059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1851963500520632230326745 1388972625390474172745059)
              ·
                refine ⟨2083458938085711259117589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1388972625390474172745059 2083458938085711259117589)
                ·
                  refine ⟨97662137722767715271137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2083458938085711259117589 97662137722767715271137)
                  ·
                    rfl

theorem cell23_1711767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 1, 6].length) (baseStart_1711767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711767 prefixEnd_1711767 := by exact prefixLift 1711767
  have htrace : WordTrace (prefixWord ++ tailWord_1711767) baseStart_1711767 baseEnd_1711767 := by
    simpa [prefixWord, tailWord_1711767, baseEnd_1711767] using wordTrace_append hprefix tailTrace_1711767
  have hstable : (prefixWord ++ tailWord_1711767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711767).length < 2 ^ (prefixWord ++ tailWord_1711767).sum := by decide
  have hdescent : baseEnd_1711767 < baseStart_1711767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711780 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_1711780 : Nat := 118140960795 + 1711780 * 2 ^ 59
def prefixEnd_1711780 : Nat := 4983230072969 + 3 ^ 40 * 1711780 * 2
def baseEnd_1711780 : Nat := 292988638251139295525891

theorem tailTrace_1711780 : CollatzResearch.WordTrace tailWord_1711780 prefixEnd_1711780 292988638251139295525891 := by
  unfold tailWord_1711780
  simp only [CollatzResearch.WordTrace]
  refine ⟨31216872869260441797018397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41622497159013922396024529 31216872869260441797018397)
  ·
    refine ⟨11706327325972665673881899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31216872869260441797018397 11706327325972665673881899)
    ·
      refine ⟨17559490988958998510822849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11706327325972665673881899 17559490988958998510822849)
      ·
        refine ⟨13169618241719248883117137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17559490988958998510822849 13169618241719248883117137)
        ·
          refine ⟨9877213681289436662337853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13169618241719248883117137 9877213681289436662337853)
          ·
            refine ⟨3703955130483538748376695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9877213681289436662337853 3703955130483538748376695)
            ·
              refine ⟨5555932695725308122565043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3703955130483538748376695 5555932695725308122565043)
              ·
                refine ⟨8333899043587962183847565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5555932695725308122565043 8333899043587962183847565)
                ·
                  refine ⟨3125212141345485818942837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8333899043587962183847565 3125212141345485818942837)
                  ·
                    refine ⟨292988638251139295525891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3125212141345485818942837 292988638251139295525891)
                    ·
                      rfl

theorem cell23_1711780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_1711780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711780 prefixEnd_1711780 := by exact prefixLift 1711780
  have htrace : WordTrace (prefixWord ++ tailWord_1711780) baseStart_1711780 baseEnd_1711780 := by
    simpa [prefixWord, tailWord_1711780, baseEnd_1711780] using wordTrace_append hprefix tailTrace_1711780
  have hstable : (prefixWord ++ tailWord_1711780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711780).length < 2 ^ (prefixWord ++ tailWord_1711780).sum := by decide
  have hdescent : baseEnd_1711780 < baseStart_1711780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711800 : List Nat := [2, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_1711800 : Nat := 118140960795 + 1711800 * 2 ^ 59
def prefixEnd_1711800 : Nat := 4983230072969 + 3 ^ 40 * 1711800 * 2
def baseEnd_1711800 : Nat := 878976184366507808327581

theorem tailTrace_1711800 : CollatzResearch.WordTrace tailWord_1711800 prefixEnd_1711800 878976184366507808327581 := by
  unfold tailWord_1711800
  simp only [CollatzResearch.WordTrace]
  refine ⟨31217237599224213504882427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41622983465632284673176569 31217237599224213504882427)
  ·
    refine ⟨46825856398836320257323641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31217237599224213504882427 46825856398836320257323641)
    ·
      refine ⟨35119392299127240192992731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46825856398836320257323641 35119392299127240192992731)
      ·
        refine ⟨52679088448690860289489097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35119392299127240192992731 52679088448690860289489097)
        ·
          refine ⟨39509316336518145217116823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52679088448690860289489097 39509316336518145217116823)
          ·
            refine ⟨59263974504777217825675235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39509316336518145217116823 59263974504777217825675235)
            ·
              refine ⟨88895961757165826738512853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59263974504777217825675235 88895961757165826738512853)
              ·
                refine ⟨2083499103683574064183895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 88895961757165826738512853 2083499103683574064183895)
                ·
                  refine ⟨3125248655525361096275843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083499103683574064183895 3125248655525361096275843)
                  ·
                    refine ⟨4687872983288041644413765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125248655525361096275843 4687872983288041644413765)
                    ·
                      refine ⟨878976184366507808327581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4687872983288041644413765 878976184366507808327581)
                      ·
                        rfl

theorem cell23_1711800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_1711800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711800 prefixEnd_1711800 := by exact prefixLift 1711800
  have htrace : WordTrace (prefixWord ++ tailWord_1711800) baseStart_1711800 baseEnd_1711800 := by
    simpa [prefixWord, tailWord_1711800, baseEnd_1711800] using wordTrace_append hprefix tailTrace_1711800
  have hstable : (prefixWord ++ tailWord_1711800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711800).length < 2 ^ (prefixWord ++ tailWord_1711800).sum := by decide
  have hdescent : baseEnd_1711800 < baseStart_1711800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711814 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1711814 : Nat := 118140960795 + 1711814 * 2 ^ 59
def prefixEnd_1711814 : Nat := 4983230072969 + 3 ^ 40 * 1711814 * 2
def baseEnd_1711814 : Nat := 292994457698556917850839

theorem tailTrace_1711814 : CollatzResearch.WordTrace tailWord_1711814 prefixEnd_1711814 292994457698556917850839 := by
  unfold tailWord_1711814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951093306887428356274203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41623323880265138267182997 1951093306887428356274203)
  ·
    refine ⟨2926639960331142534411305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1951093306887428356274203 2926639960331142534411305)
    ·
      refine ⟨2194979970248356900808479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2926639960331142534411305 2194979970248356900808479)
      ·
        refine ⟨3292469955372535351212719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2194979970248356900808479 3292469955372535351212719)
        ·
          refine ⟨4938704933058803026819079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292469955372535351212719 4938704933058803026819079)
          ·
            refine ⟨7408057399588204540228619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938704933058803026819079 7408057399588204540228619)
            ·
              refine ⟨11112086099382306810342929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408057399588204540228619 11112086099382306810342929)
              ·
                refine ⟨8334064574536730107757197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11112086099382306810342929 8334064574536730107757197)
                ·
                  refine ⟨3125274215451273790408949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8334064574536730107757197 3125274215451273790408949)
                  ·
                    refine ⟨292994457698556917850839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3125274215451273790408949 292994457698556917850839)
                    ·
                      rfl

theorem cell23_1711814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1711814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711814 prefixEnd_1711814 := by exact prefixLift 1711814
  have htrace : WordTrace (prefixWord ++ tailWord_1711814) baseStart_1711814 baseEnd_1711814 := by
    simpa [prefixWord, tailWord_1711814, baseEnd_1711814] using wordTrace_append hprefix tailTrace_1711814
  have hstable : (prefixWord ++ tailWord_1711814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711814).length < 2 ^ (prefixWord ++ tailWord_1711814).sum := by decide
  have hdescent : baseEnd_1711814 < baseStart_1711814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711834 : List Nat := [3, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2]
def baseStart_1711834 : Nat := 118140960795 + 1711834 * 2 ^ 59
def prefixEnd_1711834 : Nat := 4983230072969 + 3 ^ 40 * 1711834 * 2
def baseEnd_1711834 : Nat := 878993642708760675302425

theorem tailTrace_1711834 : CollatzResearch.WordTrace tailWord_1711834 prefixEnd_1711834 878993642708760675302425 := by
  unfold tailWord_1711834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15608928820081312704125639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41623810186883500544335037 15608928820081312704125639)
  ·
    refine ⟨23413393230121969056188459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15608928820081312704125639 23413393230121969056188459)
    ·
      refine ⟨35120089845182953584282689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23413393230121969056188459 35120089845182953584282689)
      ·
        refine ⟨26340067383887215188212017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35120089845182953584282689 26340067383887215188212017)
        ·
          refine ⟨19755050537915411391159013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26340067383887215188212017 19755050537915411391159013)
          ·
            refine ⟨3704071975859139635842315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19755050537915411391159013 3704071975859139635842315)
            ·
              refine ⟨5556107963788709453763473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704071975859139635842315 5556107963788709453763473)
              ·
                refine ⟨4167080972841532090322605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5556107963788709453763473 4167080972841532090322605)
                ·
                  refine ⟨1562655364815574533870977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4167080972841532090322605 1562655364815574533870977)
                  ·
                    refine ⟨1171991523611680900403233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1562655364815574533870977 1171991523611680900403233)
                    ·
                      refine ⟨878993642708760675302425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1171991523611680900403233 878993642708760675302425)
                      ·
                        rfl

theorem cell23_1711834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 2, 3, 2, 2].length) (baseStart_1711834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711834 prefixEnd_1711834 := by exact prefixLift 1711834
  have htrace : WordTrace (prefixWord ++ tailWord_1711834) baseStart_1711834 baseEnd_1711834 := by
    simpa [prefixWord, tailWord_1711834, baseEnd_1711834] using wordTrace_append hprefix tailTrace_1711834
  have hstable : (prefixWord ++ tailWord_1711834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711834).length < 2 ^ (prefixWord ++ tailWord_1711834).sum := by decide
  have hdescent : baseEnd_1711834 < baseStart_1711834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711867 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 3]
def baseStart_1711867 : Nat := 118140960795 + 1711867 * 2 ^ 59
def prefixEnd_1711867 : Nat := 4983230072969 + 3 ^ 40 * 1711867 * 2
def baseEnd_1711867 : Nat := 879010587570359046189773

theorem tailTrace_1711867 : CollatzResearch.WordTrace tailWord_1711867 prefixEnd_1711867 879010587570359046189773 := by
  unfold tailWord_1711867
  simp only [CollatzResearch.WordTrace]
  refine ⟨62436918889205697452453855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41624612592803798301635903 62436918889205697452453855)
  ·
    refine ⟨93655378333808546178680783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62436918889205697452453855 93655378333808546178680783)
    ·
      refine ⟨140483067500712819268021175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93655378333808546178680783 140483067500712819268021175)
      ·
        refine ⟨210724601251069228902031763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140483067500712819268021175 210724601251069228902031763)
        ·
          refine ⟨316086901876603843353047645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210724601251069228902031763 316086901876603843353047645)
          ·
            refine ⟨118532588203726441257392867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 316086901876603843353047645 118532588203726441257392867)
            ·
              refine ⟨177798882305589661886089301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118532588203726441257392867 177798882305589661886089301)
              ·
                refine ⟨2083580652018628850227609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 177798882305589661886089301 2083580652018628850227609)
                ·
                  refine ⟨1562685489013971637670707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2083580652018628850227609 1562685489013971637670707)
                  ·
                    refine ⟨2344028233520957456506061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562685489013971637670707 2344028233520957456506061)
                    ·
                      refine ⟨879010587570359046189773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344028233520957456506061 879010587570359046189773)
                      ·
                        rfl

theorem cell23_1711867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 1, 3].length) (baseStart_1711867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711867 prefixEnd_1711867 := by exact prefixLift 1711867
  have htrace : WordTrace (prefixWord ++ tailWord_1711867) baseStart_1711867 baseEnd_1711867 := by
    simpa [prefixWord, tailWord_1711867, baseEnd_1711867] using wordTrace_append hprefix tailTrace_1711867
  have hstable : (prefixWord ++ tailWord_1711867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711867).length < 2 ^ (prefixWord ++ tailWord_1711867).sum := by decide
  have hdescent : baseEnd_1711867 < baseStart_1711867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711885 : List Nat := [1, 7, 2, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_1711885 : Nat := 118140960795 + 1711885 * 2 ^ 59
def prefixEnd_1711885 : Nat := 4983230072969 + 3 ^ 40 * 1711885 * 2
def baseEnd_1711885 : Nat := 879019830222139975764691

theorem tailTrace_1711885 : CollatzResearch.WordTrace tailWord_1711885 prefixEnd_1711885 879019830222139975764691 := by
  unfold tailWord_1711885
  simp only [CollatzResearch.WordTrace]
  refine ⟨62437575403140486526609109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41625050268760324351072739 62437575403140486526609109)
  ·
    refine ⟨1463380673511105152967401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 62437575403140486526609109 1463380673511105152967401)
    ·
      refine ⟨1097535505133328864725551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1463380673511105152967401 1097535505133328864725551)
      ·
        refine ⟨1646303257699993297088327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097535505133328864725551 1646303257699993297088327)
        ·
          refine ⟨2469454886549989945632491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646303257699993297088327 2469454886549989945632491)
          ·
            refine ⟨3704182329824984918448737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469454886549989945632491 3704182329824984918448737)
            ·
              refine ⟨2778136747368738688836553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704182329824984918448737 2778136747368738688836553)
              ·
                refine ⟨2083602560526554016627415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778136747368738688836553 2083602560526554016627415)
                ·
                  refine ⟨3125403840789831024941123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083602560526554016627415 3125403840789831024941123)
                  ·
                    refine ⟨4688105761184746537411685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125403840789831024941123 4688105761184746537411685)
                    ·
                      refine ⟨879019830222139975764691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4688105761184746537411685 879019830222139975764691)
                      ·
                        rfl

theorem cell23_1711885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_1711885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711885 prefixEnd_1711885 := by exact prefixLift 1711885
  have htrace : WordTrace (prefixWord ++ tailWord_1711885) baseStart_1711885 baseEnd_1711885 := by
    simpa [prefixWord, tailWord_1711885, baseEnd_1711885] using wordTrace_append hprefix tailTrace_1711885
  have hstable : (prefixWord ++ tailWord_1711885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711885).length < 2 ^ (prefixWord ++ tailWord_1711885).sum := by decide
  have hdescent : baseEnd_1711885 < baseStart_1711885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711907 : List Nat := [1, 1, 1, 4, 2, 1, 2, 4, 1, 4, 2]
def baseStart_1711907 : Nat := 118140960795 + 1711907 * 2 ^ 59
def prefixEnd_1711907 : Nat := 4983230072969 + 3 ^ 40 * 1711907 * 2
def baseEnd_1711907 : Nat := 879031126796538889689589

theorem tailTrace_1711907 : CollatzResearch.WordTrace tailWord_1711907 prefixEnd_1711907 879031126796538889689589 := by
  unfold tailWord_1711907
  simp only [CollatzResearch.WordTrace]
  refine ⟨62438377809060784283909975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41625585206040522855939983 62438377809060784283909975)
  ·
    refine ⟨93657566713591176425864963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62438377809060784283909975 93657566713591176425864963)
    ·
      refine ⟨140486350070386764638797445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93657566713591176425864963 140486350070386764638797445)
      ·
        refine ⟨26341190638197518369774521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140486350070386764638797445 26341190638197518369774521)
        ·
          refine ⟨19755892978648138777330891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26341190638197518369774521 19755892978648138777330891)
          ·
            refine ⟨29633839467972208165996337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755892978648138777330891 29633839467972208165996337)
            ·
              refine ⟨22225379600979156124497253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29633839467972208165996337 22225379600979156124497253)
              ·
                refine ⟨4167258675183591773343235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22225379600979156124497253 4167258675183591773343235)
                ·
                  refine ⟨6250888012775387660014853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167258675183591773343235 6250888012775387660014853)
                  ·
                    refine ⟨1172041502395385186252785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6250888012775387660014853 1172041502395385186252785)
                    ·
                      refine ⟨879031126796538889689589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172041502395385186252785 879031126796538889689589)
                      ·
                        rfl

theorem cell23_1711907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_1711907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1711907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1711907 prefixEnd_1711907 := by exact prefixLift 1711907
  have htrace : WordTrace (prefixWord ++ tailWord_1711907) baseStart_1711907 baseEnd_1711907 := by
    simpa [prefixWord, tailWord_1711907, baseEnd_1711907] using wordTrace_append hprefix tailTrace_1711907
  have hstable : (prefixWord ++ tailWord_1711907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711907).length < 2 ^ (prefixWord ++ tailWord_1711907).sum := by decide
  have hdescent : baseEnd_1711907 < baseStart_1711907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712064 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3]
def baseStart_1712064 : Nat := 118140960795 + 1712064 * 2 ^ 59
def prefixEnd_1712064 : Nat := 4983230072969 + 3 ^ 40 * 1712064 * 2
def baseEnd_1712064 : Nat := 879111743259294775426367

theorem tailTrace_1712064 : CollatzResearch.WordTrace tailWord_1712064 prefixEnd_1712064 879111743259294775426367 := by
  unfold tailWord_1712064
  simp only [CollatzResearch.WordTrace]
  refine ⟨31222052034746000048687623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41629402712994666731583497 31222052034746000048687623)
  ·
    refine ⟨46833078052119000073031435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31222052034746000048687623 46833078052119000073031435)
    ·
      refine ⟨70249617078178500109547153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46833078052119000073031435 70249617078178500109547153)
      ·
        refine ⟨52687212808633875082160365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70249617078178500109547153 52687212808633875082160365)
        ·
          refine ⟨19757704803237703155810137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52687212808633875082160365 19757704803237703155810137)
          ·
            refine ⟨14818278602428277366857603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19757704803237703155810137 14818278602428277366857603)
            ·
              refine ⟨22227417903642416050286405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14818278602428277366857603 22227417903642416050286405)
              ·
                refine ⟨4167640856932953009428701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22227417903642416050286405 4167640856932953009428701)
                ·
                  refine ⟨1562865321349857378535763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4167640856932953009428701 1562865321349857378535763)
                  ·
                    refine ⟨2344297982024786067803645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562865321349857378535763 2344297982024786067803645)
                    ·
                      refine ⟨879111743259294775426367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344297982024786067803645 879111743259294775426367)
                      ·
                        rfl

theorem cell23_1712064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_1712064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712064 prefixEnd_1712064 := by exact prefixLift 1712064
  have htrace : WordTrace (prefixWord ++ tailWord_1712064) baseStart_1712064 baseEnd_1712064 := by
    simpa [prefixWord, tailWord_1712064, baseEnd_1712064] using wordTrace_append hprefix tailTrace_1712064
  have hstable : (prefixWord ++ tailWord_1712064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712064).length < 2 ^ (prefixWord ++ tailWord_1712064).sum := by decide
  have hdescent : baseEnd_1712064 < baseStart_1712064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712074 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2]
def baseStart_1712074 : Nat := 118140960795 + 1712074 * 2 ^ 59
def prefixEnd_1712074 : Nat := 4983230072969 + 3 ^ 40 * 1712074 * 2
def baseEnd_1712074 : Nat := 879116878065839736301321

theorem tailTrace_1712074 : CollatzResearch.WordTrace tailWord_1712074 prefixEnd_1712074 879116878065839736301321 := by
  unfold tailWord_1712074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611117199863942951309819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41629645866303847870159517 15611117199863942951309819)
  ·
    refine ⟨23416675799795914426964729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15611117199863942951309819 23416675799795914426964729)
    ·
      refine ⟨17562506849846935820223547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23416675799795914426964729 17562506849846935820223547)
      ·
        refine ⟨26343760274770403730335321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17562506849846935820223547 26343760274770403730335321)
        ·
          refine ⟨19757820206077802797751491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26343760274770403730335321 19757820206077802797751491)
          ·
            refine ⟨29636730309116704196627237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19757820206077802797751491 29636730309116704196627237)
            ·
              refine ⟨5556886932959382036867607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29636730309116704196627237 5556886932959382036867607)
              ·
                refine ⟨8335330399439073055301411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5556886932959382036867607 8335330399439073055301411)
                ·
                  refine ⟨12502995599158609582952117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8335330399439073055301411 12502995599158609582952117)
                  ·
                    refine ⟨1172155837421119648401761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12502995599158609582952117 1172155837421119648401761)
                    ·
                      refine ⟨879116878065839736301321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172155837421119648401761 879116878065839736301321)
                      ·
                        rfl

theorem cell23_1712074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_1712074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712074 prefixEnd_1712074 := by exact prefixLift 1712074
  have htrace : WordTrace (prefixWord ++ tailWord_1712074) baseStart_1712074 baseEnd_1712074 := by
    simpa [prefixWord, tailWord_1712074, baseEnd_1712074] using wordTrace_append hprefix tailTrace_1712074
  have hstable : (prefixWord ++ tailWord_1712074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712074).length < 2 ^ (prefixWord ++ tailWord_1712074).sum := by decide
  have hdescent : baseEnd_1712074 < baseStart_1712074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712081 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 1, 1, 3]
def baseStart_1712081 : Nat := 118140960795 + 1712081 * 2 ^ 59
def prefixEnd_1712081 : Nat := 4983230072969 + 3 ^ 40 * 1712081 * 2
def baseEnd_1712081 : Nat := 879120472430421208913789

theorem tailTrace_1712081 : CollatzResearch.WordTrace tailWord_1712081 prefixEnd_1712081 879120472430421208913789 := by
  unfold tailWord_1712081
  simp only [CollatzResearch.WordTrace]
  refine ⟨62444724110430412000744097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41629816073620274667162731 62444724110430412000744097)
  ·
    refine ⟨46833543082822809000558073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62444724110430412000744097 46833543082822809000558073)
    ·
      refine ⟨35125157312117106750418555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46833543082822809000558073 35125157312117106750418555)
      ·
        refine ⟨52687735968175660125627833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35125157312117106750418555 52687735968175660125627833)
        ·
          refine ⟨39515801976131745094220875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52687735968175660125627833 39515801976131745094220875)
          ·
            refine ⟨59273702964197617641331313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39515801976131745094220875 59273702964197617641331313)
            ·
              refine ⟨44455277223148213230998485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59273702964197617641331313 44455277223148213230998485)
              ·
                refine ⟨1041920559917536247601527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44455277223148213230998485 1041920559917536247601527)
                ·
                  refine ⟨1562880839876304371402291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041920559917536247601527 1562880839876304371402291)
                  ·
                    refine ⟨2344321259814456557103437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1562880839876304371402291 2344321259814456557103437)
                    ·
                      refine ⟨879120472430421208913789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344321259814456557103437 879120472430421208913789)
                      ·
                        rfl

theorem cell23_1712081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 1, 3].length) (baseStart_1712081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712081 prefixEnd_1712081 := by exact prefixLift 1712081
  have htrace : WordTrace (prefixWord ++ tailWord_1712081) baseStart_1712081 baseEnd_1712081 := by
    simpa [prefixWord, tailWord_1712081, baseEnd_1712081] using wordTrace_append hprefix tailTrace_1712081
  have hstable : (prefixWord ++ tailWord_1712081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712081).length < 2 ^ (prefixWord ++ tailWord_1712081).sum := by decide
  have hdescent : baseEnd_1712081 < baseStart_1712081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712084 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1712084 : Nat := 118140960795 + 1712084 * 2 ^ 59
def prefixEnd_1712084 : Nat := 4983230072969 + 3 ^ 40 * 1712084 * 2
def baseEnd_1712084 : Nat := 293040670957461565725425

theorem tailTrace_1712084 : CollatzResearch.WordTrace tailWord_1712084 prefixEnd_1712084 293040670957461565725425 := by
  unfold tailWord_1712084
  simp only [CollatzResearch.WordTrace]
  refine ⟨31222416764709771756551653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41629889019613029008735537 31222416764709771756551653)
  ·
    refine ⟨5854203143383082204353435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31222416764709771756551653 5854203143383082204353435)
    ·
      refine ⟨8781304715074623306530153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854203143383082204353435 8781304715074623306530153)
      ·
        refine ⟨6585978536305967479897615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8781304715074623306530153 6585978536305967479897615)
        ·
          refine ⟨9878967804458951219846423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585978536305967479897615 9878967804458951219846423)
          ·
            refine ⟨14818451706688426829769635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878967804458951219846423 14818451706688426829769635)
            ·
              refine ⟨22227677560032640244654453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14818451706688426829769635 22227677560032640244654453)
              ·
                refine ⟨2083844771253060022936355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22227677560032640244654453 2083844771253060022936355)
                ·
                  refine ⟨3125767156879590034404533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083844771253060022936355 3125767156879590034404533)
                  ·
                    refine ⟨293040670957461565725425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3125767156879590034404533 293040670957461565725425)
                    ·
                      rfl

theorem cell23_1712084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1712084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712084 prefixEnd_1712084 := by exact prefixLift 1712084
  have htrace : WordTrace (prefixWord ++ tailWord_1712084) baseStart_1712084 baseEnd_1712084 := by
    simpa [prefixWord, tailWord_1712084, baseEnd_1712084] using wordTrace_append hprefix tailTrace_1712084
  have hstable : (prefixWord ++ tailWord_1712084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712084).length < 2 ^ (prefixWord ++ tailWord_1712084).sum := by decide
  have hdescent : baseEnd_1712084 < baseStart_1712084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712092 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1712092 : Nat := 118140960795 + 1712092 * 2 ^ 59
def prefixEnd_1712092 : Nat := 4983230072969 + 3 ^ 40 * 1712092 * 2
def baseEnd_1712092 : Nat := 293042040239206888625413

theorem tailTrace_1712092 : CollatzResearch.WordTrace tailWord_1712092 prefixEnd_1712092 293042040239206888625413 := by
  unfold tailWord_1712092
  simp only [CollatzResearch.WordTrace]
  refine ⟨31222562656695280439697265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41630083542260373919596353 31222562656695280439697265)
  ·
    refine ⟨23416921992521460329772949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31222562656695280439697265 23416921992521460329772949)
    ·
      refine ⟨1097668218399443452958107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23416921992521460329772949 1097668218399443452958107)
      ·
        refine ⟨1646502327599165179437161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097668218399443452958107 1646502327599165179437161)
        ·
          refine ⟨1234876745699373884577871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646502327599165179437161 1234876745699373884577871)
          ·
            refine ⟨1852315118549060826866807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234876745699373884577871 1852315118549060826866807)
            ·
              refine ⟨2778472677823591240300211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852315118549060826866807 2778472677823591240300211)
              ·
                refine ⟨4167709016735386860450317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778472677823591240300211 4167709016735386860450317)
                ·
                  refine ⟨1562890881275770072668869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4167709016735386860450317 1562890881275770072668869)
                  ·
                    refine ⟨293042040239206888625413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1562890881275770072668869 293042040239206888625413)
                    ·
                      rfl

theorem cell23_1712092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1712092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712092 prefixEnd_1712092 := by exact prefixLift 1712092
  have htrace : WordTrace (prefixWord ++ tailWord_1712092) baseStart_1712092 baseEnd_1712092 := by
    simpa [prefixWord, tailWord_1712092, baseEnd_1712092] using wordTrace_append hprefix tailTrace_1712092
  have hstable : (prefixWord ++ tailWord_1712092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712092).length < 2 ^ (prefixWord ++ tailWord_1712092).sum := by decide
  have hdescent : baseEnd_1712092 < baseStart_1712092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712118 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1712118 : Nat := 118140960795 + 1712118 * 2 ^ 59
def prefixEnd_1712118 : Nat := 4983230072969 + 3 ^ 40 * 1712118 * 2
def baseEnd_1712118 : Nat := 293046490404879188050373

theorem tailTrace_1712118 : CollatzResearch.WordTrace tailWord_1712118 prefixEnd_1712118 293046490404879188050373 := by
  unfold tailWord_1712118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902879600706022957490063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41630715740864244879894005 3902879600706022957490063)
  ·
    refine ⟨5854319401059034436235095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3902879600706022957490063 5854319401059034436235095)
    ·
      refine ⟨8781479101588551654352643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5854319401059034436235095 8781479101588551654352643)
      ·
        refine ⟨13172218652382827481528965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8781479101588551654352643 13172218652382827481528965)
        ·
          refine ⟨2469790997321780152786681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13172218652382827481528965 2469790997321780152786681)
          ·
            refine ⟨1852343247991335114590011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469790997321780152786681 1852343247991335114590011)
            ·
              refine ⟨2778514871987002671885017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852343247991335114590011 2778514871987002671885017)
              ·
                refine ⟨2083886153990252003913763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778514871987002671885017 2083886153990252003913763)
                ·
                  refine ⟨3125829230985378005870645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083886153990252003913763 3125829230985378005870645)
                  ·
                    refine ⟨293046490404879188050373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3125829230985378005870645 293046490404879188050373)
                    ·
                      rfl

theorem cell23_1712118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1712118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712118 prefixEnd_1712118 := by exact prefixLift 1712118
  have htrace : WordTrace (prefixWord ++ tailWord_1712118) baseStart_1712118 baseEnd_1712118 := by
    simpa [prefixWord, tailWord_1712118, baseEnd_1712118] using wordTrace_append hprefix tailTrace_1712118
  have hstable : (prefixWord ++ tailWord_1712118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712118).length < 2 ^ (prefixWord ++ tailWord_1712118).sum := by decide
  have hdescent : baseEnd_1712118 < baseStart_1712118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712121 : List Nat := [1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_1712121 : Nat := 118140960795 + 1712121 * 2 ^ 59
def prefixEnd_1712121 : Nat := 4983230072969 + 3 ^ 40 * 1712121 * 2
def baseEnd_1712121 : Nat := 879141011656601052413605

theorem tailTrace_1712121 : CollatzResearch.WordTrace tailWord_1712121 prefixEnd_1712121 879141011656601052413605 := by
  unfold tailWord_1712121
  simp only [CollatzResearch.WordTrace]
  refine ⟨62446183030285498832200217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41630788686856999221466811 62446183030285498832200217)
  ·
    refine ⟨46834637272714124124150163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62446183030285498832200217 46834637272714124124150163)
    ·
      refine ⟨70251955909071186186225245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46834637272714124124150163 70251955909071186186225245)
      ·
        refine ⟨26344483465901694819834467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70251955909071186186225245 26344483465901694819834467)
        ·
          refine ⟨39516725198852542229751701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26344483465901694819834467 39516725198852542229751701)
          ·
            refine ⟨1852346493696212917019611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39516725198852542229751701 1852346493696212917019611)
            ·
              refine ⟨2778519740544319375529417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852346493696212917019611 2778519740544319375529417)
              ·
                refine ⟨2083889805408239531647063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778519740544319375529417 2083889805408239531647063)
                ·
                  refine ⟨3125834708112359297470595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083889805408239531647063 3125834708112359297470595)
                  ·
                    refine ⟨4688752062168538946205893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125834708112359297470595 4688752062168538946205893)
                    ·
                      refine ⟨879141011656601052413605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4688752062168538946205893 879141011656601052413605)
                      ·
                        rfl

theorem cell23_1712121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_1712121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712121 prefixEnd_1712121 := by exact prefixLift 1712121
  have htrace : WordTrace (prefixWord ++ tailWord_1712121) baseStart_1712121 baseEnd_1712121 := by
    simpa [prefixWord, tailWord_1712121, baseEnd_1712121] using wordTrace_append hprefix tailTrace_1712121
  have hstable : (prefixWord ++ tailWord_1712121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712121).length < 2 ^ (prefixWord ++ tailWord_1712121).sum := by decide
  have hdescent : baseEnd_1712121 < baseStart_1712121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712124 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_1712124 : Nat := 118140960795 + 1712124 * 2 ^ 59
def prefixEnd_1712124 : Nat := 4983230072969 + 3 ^ 40 * 1712124 * 2
def baseEnd_1712124 : Nat := 879142552098564540676091

theorem tailTrace_1712124 : CollatzResearch.WordTrace tailWord_1712124 prefixEnd_1712124 879142552098564540676091 := by
  unfold tailWord_1712124
  simp only [CollatzResearch.WordTrace]
  refine ⟨31223146224637315172279713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41630861632849753563039617 31223146224637315172279713)
  ·
    refine ⟨23417359668477986379209785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31223146224637315172279713 23417359668477986379209785)
    ·
      refine ⟨17563019751358489784407339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23417359668477986379209785 17563019751358489784407339)
      ·
        refine ⟨26344529627037734676611009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17563019751358489784407339 26344529627037734676611009)
        ·
          refine ⟨19758397220278301007458257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26344529627037734676611009 19758397220278301007458257)
          ·
            refine ⟨14818797915208725755593693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19758397220278301007458257 14818797915208725755593693)
            ·
              refine ⟨5557049218203272158347635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14818797915208725755593693 5557049218203272158347635)
              ·
                refine ⟨8335573827304908237521453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557049218203272158347635 8335573827304908237521453)
                ·
                  refine ⟨3125840185239340589070545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8335573827304908237521453 3125840185239340589070545)
                  ·
                    refine ⟨2344380138929505441802909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3125840185239340589070545 2344380138929505441802909)
                    ·
                      refine ⟨879142552098564540676091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344380138929505441802909 879142552098564540676091)
                      ·
                        rfl

theorem cell23_1712124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_1712124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712124 prefixEnd_1712124 := by exact prefixLift 1712124
  have htrace : WordTrace (prefixWord ++ tailWord_1712124) baseStart_1712124 baseEnd_1712124 := by
    simpa [prefixWord, tailWord_1712124, baseEnd_1712124] using wordTrace_append hprefix tailTrace_1712124
  have hstable : (prefixWord ++ tailWord_1712124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712124).length < 2 ^ (prefixWord ++ tailWord_1712124).sum := by decide
  have hdescent : baseEnd_1712124 < baseStart_1712124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712138 : List Nat := [3, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4]
def baseStart_1712138 : Nat := 118140960795 + 1712138 * 2 ^ 59
def prefixEnd_1712138 : Nat := 4983230072969 + 3 ^ 40 * 1712138 * 2
def baseEnd_1712138 : Nat := 879149740827727485901027

theorem tailTrace_1712138 : CollatzResearch.WordTrace tailWord_1712138 prefixEnd_1712138 879149740827727485901027 := by
  unfold tailWord_1712138
  simp only [CollatzResearch.WordTrace]
  refine ⟨15611700767805977683892267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41631202047482607157046045 15611700767805977683892267)
  ·
    refine ⟨23417551151708966525838401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15611700767805977683892267 23417551151708966525838401)
    ·
      refine ⟨17563163363781724894378801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23417551151708966525838401 17563163363781724894378801)
      ·
        refine ⟨13172372522836293670784101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17563163363781724894378801 13172372522836293670784101)
        ·
          refine ⟨2469819848031805063272019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13172372522836293670784101 2469819848031805063272019)
          ·
            refine ⟨3704729772047707594908029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469819848031805063272019 3704729772047707594908029)
            ·
              refine ⟨1389273664517890348090511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3704729772047707594908029 1389273664517890348090511)
              ·
                refine ⟨2083910496776835522135767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389273664517890348090511 2083910496776835522135767)
                ·
                  refine ⟨3125865745165253283203651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083910496776835522135767 3125865745165253283203651)
                  ·
                    refine ⟨4688798617747879924805477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3125865745165253283203651 4688798617747879924805477)
                    ·
                      refine ⟨879149740827727485901027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4688798617747879924805477 879149740827727485901027)
                      ·
                        rfl

theorem cell23_1712138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_1712138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712138 prefixEnd_1712138 := by exact prefixLift 1712138
  have htrace : WordTrace (prefixWord ++ tailWord_1712138) baseStart_1712138 baseEnd_1712138 := by
    simpa [prefixWord, tailWord_1712138, baseEnd_1712138] using wordTrace_append hprefix tailTrace_1712138
  have hstable : (prefixWord ++ tailWord_1712138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712138).length < 2 ^ (prefixWord ++ tailWord_1712138).sum := by decide
  have hdescent : baseEnd_1712138 < baseStart_1712138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712161 : List Nat := [1, 2, 3, 2, 5, 1, 1, 8]
def baseStart_1712161 : Nat := 118140960795 + 1712161 * 2 ^ 59
def prefixEnd_1712161 : Nat := 4983230072969 + 3 ^ 40 * 1712161 * 2
def baseEnd_1712161 : Nat := 32561538921584477626423

theorem tailTrace_1712161 : CollatzResearch.WordTrace tailWord_1712161 prefixEnd_1712161 32561538921584477626423 := by
  unfold tailWord_1712161
  simp only [CollatzResearch.WordTrace]
  refine ⟨62447641950140585663656337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41631761300093723775770891 62447641950140585663656337)
  ·
    refine ⟨46835731462605439247742253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62447641950140585663656337 46835731462605439247742253)
    ·
      refine ⟨17563399298477039717903345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46835731462605439247742253 17563399298477039717903345)
      ·
        refine ⟨13172549473857779788427509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17563399298477039717903345 13172549473857779788427509)
        ·
          refine ⟨1234926513174166855165079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13172549473857779788427509 1234926513174166855165079)
          ·
            refine ⟨1852389769761250282747619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234926513174166855165079 1852389769761250282747619)
            ·
              refine ⟨2778584654641875424121429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852389769761250282747619 2778584654641875424121429)
              ·
                refine ⟨32561538921584477626423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2778584654641875424121429 32561538921584477626423)
                ·
                  rfl

theorem cell23_1712161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 8].length) (baseStart_1712161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712161 prefixEnd_1712161 := by exact prefixLift 1712161
  have htrace : WordTrace (prefixWord ++ tailWord_1712161) baseStart_1712161 baseEnd_1712161 := by
    simpa [prefixWord, tailWord_1712161, baseEnd_1712161] using wordTrace_append hprefix tailTrace_1712161
  have hstable : (prefixWord ++ tailWord_1712161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712161).length < 2 ^ (prefixWord ++ tailWord_1712161).sum := by decide
  have hdescent : baseEnd_1712161 < baseStart_1712161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712168 : List Nat := [2, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1712168 : Nat := 118140960795 + 1712168 * 2 ^ 59
def prefixEnd_1712168 : Nat := 4983230072969 + 3 ^ 40 * 1712168 * 2
def baseEnd_1712168 : Nat := 879165145247362368525889

theorem tailTrace_1712168 : CollatzResearch.WordTrace tailWord_1712168 prefixEnd_1712168 879165145247362368525889 := by
  unfold tailWord_1712168
  simp only [CollatzResearch.WordTrace]
  refine ⟨31223948630557612929580579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41631931507410150572774105 31223948630557612929580579)
  ·
    refine ⟨46835922945836419394370869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31223948630557612929580579 46835922945836419394370869)
    ·
      refine ⟨4390867776172164318222269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46835922945836419394370869 4390867776172164318222269)
      ·
        refine ⟨1646575416064561619333351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4390867776172164318222269 1646575416064561619333351)
        ·
          refine ⟨2469863124096842429000027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646575416064561619333351 2469863124096842429000027)
          ·
            refine ⟨3704794686145263643500041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469863124096842429000027 3704794686145263643500041)
            ·
              refine ⟨2778596014608947732625031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704794686145263643500041 2778596014608947732625031)
              ·
                refine ⟨4167894021913421598937547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778596014608947732625031 4167894021913421598937547)
                ·
                  refine ⟨6251841032870132398406321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167894021913421598937547 6251841032870132398406321)
                  ·
                    refine ⟨4688880774652599298804741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6251841032870132398406321 4688880774652599298804741)
                    ·
                      refine ⟨879165145247362368525889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4688880774652599298804741 879165145247362368525889)
                      ·
                        rfl

theorem cell23_1712168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1712168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712168 prefixEnd_1712168 := by exact prefixLift 1712168
  have htrace : WordTrace (prefixWord ++ tailWord_1712168) baseStart_1712168 baseEnd_1712168 := by
    simpa [prefixWord, tailWord_1712168, baseEnd_1712168] using wordTrace_append hprefix tailTrace_1712168
  have hstable : (prefixWord ++ tailWord_1712168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712168).length < 2 ^ (prefixWord ++ tailWord_1712168).sum := by decide
  have hdescent : baseEnd_1712168 < baseStart_1712168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712181 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_1712181 : Nat := 118140960795 + 1712181 * 2 ^ 59
def prefixEnd_1712181 : Nat := 4983230072969 + 3 ^ 40 * 1712181 * 2
def baseEnd_1712181 : Nat := 879171820495870817663329

theorem tailTrace_1712181 : CollatzResearch.WordTrace tailWord_1712181 prefixEnd_1712181 879171820495870817663329 := by
  unfold tailWord_1712181
  simp only [CollatzResearch.WordTrace]
  refine ⟨62448371410068129079384397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41632247606712086052922931 62448371410068129079384397)
  ·
    refine ⟨23418139278775548404769149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62448371410068129079384397 23418139278775548404769149)
    ·
      refine ⟨8781802229540830651788431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23418139278775548404769149 8781802229540830651788431)
      ·
        refine ⟨13172703344311245977682647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8781802229540830651788431 13172703344311245977682647)
        ·
          refine ⟨19759055016466868966523971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13172703344311245977682647 19759055016466868966523971)
          ·
            refine ⟨29638582524700303449785957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19759055016466868966523971 29638582524700303449785957)
            ·
              refine ⟨5557234223381306896834867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29638582524700303449785957 5557234223381306896834867)
              ·
                refine ⟨8335851335071960345252301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557234223381306896834867 8335851335071960345252301)
                ·
                  refine ⟨3125944250651985129469613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8335851335071960345252301 3125944250651985129469613)
                  ·
                    refine ⟨1172229093994494423551105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3125944250651985129469613 1172229093994494423551105)
                    ·
                      refine ⟨879171820495870817663329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172229093994494423551105 879171820495870817663329)
                      ·
                        rfl

theorem cell23_1712181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_1712181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712181 prefixEnd_1712181 := by exact prefixLift 1712181
  have htrace : WordTrace (prefixWord ++ tailWord_1712181) baseStart_1712181 baseEnd_1712181 := by
    simpa [prefixWord, tailWord_1712181, baseEnd_1712181] using wordTrace_append hprefix tailTrace_1712181
  have hstable : (prefixWord ++ tailWord_1712181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712181).length < 2 ^ (prefixWord ++ tailWord_1712181).sum := by decide
  have hdescent : baseEnd_1712181 < baseStart_1712181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712197 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1712197 : Nat := 118140960795 + 1712197 * 2 ^ 59
def prefixEnd_1712197 : Nat := 4983230072969 + 3 ^ 40 * 1712197 * 2
def baseEnd_1712197 : Nat := 879180036186342755063255

theorem tailTrace_1712197 : CollatzResearch.WordTrace tailWord_1712197 prefixEnd_1712197 879180036186342755063255 := by
  unfold tailWord_1712197
  simp only [CollatzResearch.WordTrace]
  refine ⟨62448954978010163811966845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41632636652006775874644563 62448954978010163811966845)
  ·
    refine ⟨23418358116753811429487567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62448954978010163811966845 23418358116753811429487567)
    ·
      refine ⟨35127537175130717144231351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23418358116753811429487567 35127537175130717144231351)
      ·
        refine ⟨52691305762696075716347027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35127537175130717144231351 52691305762696075716347027)
        ·
          refine ⟨79036958644044113574520541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52691305762696075716347027 79036958644044113574520541)
          ·
            refine ⟨29638859491516542590445203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79036958644044113574520541 29638859491516542590445203)
            ·
              refine ⟨44458289237274813885667805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29638859491516542590445203 44458289237274813885667805)
              ·
                refine ⟨16671858463978055207125427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44458289237274813885667805 16671858463978055207125427)
                ·
                  refine ⟨25007787695967082810688141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16671858463978055207125427 25007787695967082810688141)
                  ·
                    refine ⟨9377920385987656054008053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25007787695967082810688141 9377920385987656054008053)
                    ·
                      refine ⟨879180036186342755063255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9377920385987656054008053 879180036186342755063255)
                      ·
                        rfl

theorem cell23_1712197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1712197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712197 prefixEnd_1712197 := by exact prefixLift 1712197
  have htrace : WordTrace (prefixWord ++ tailWord_1712197) baseStart_1712197 baseEnd_1712197 := by
    simpa [prefixWord, tailWord_1712197, baseEnd_1712197] using wordTrace_append hprefix tailTrace_1712197
  have hstable : (prefixWord ++ tailWord_1712197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712197).length < 2 ^ (prefixWord ++ tailWord_1712197).sum := by decide
  have hdescent : baseEnd_1712197 < baseStart_1712197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712207 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4]
def baseStart_1712207 : Nat := 118140960795 + 1712207 * 2 ^ 59
def prefixEnd_1712207 : Nat := 4983230072969 + 3 ^ 40 * 1712207 * 2
def baseEnd_1712207 : Nat := 879185170992887715938209

theorem tailTrace_1712207 : CollatzResearch.WordTrace tailWord_1712207 prefixEnd_1712207 879185170992887715938209 := by
  unfold tailWord_1712207
  simp only [CollatzResearch.WordTrace]
  refine ⟨62449319707973935519830875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41632879805315957013220583 62449319707973935519830875)
  ·
    refine ⟨93673979561960903279746313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62449319707973935519830875 93673979561960903279746313)
    ·
      refine ⟨70255484671470677459809735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93673979561960903279746313 70255484671470677459809735)
      ·
        refine ⟨105383227007206016189714603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70255484671470677459809735 105383227007206016189714603)
        ·
          refine ⟨158074840510809024284571905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105383227007206016189714603 158074840510809024284571905)
          ·
            refine ⟨118556130383106768213428929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158074840510809024284571905 118556130383106768213428929)
            ·
              refine ⟨88917097787330076160071697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118556130383106768213428929 88917097787330076160071697)
              ·
                refine ⟨66687823340497557120053773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88917097787330076160071697 66687823340497557120053773)
                ·
                  refine ⟨25007933752686583920020165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66687823340497557120053773 25007933752686583920020165)
                  ·
                    refine ⟨4688987578628734485003781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25007933752686583920020165 4688987578628734485003781)
                    ·
                      refine ⟨879185170992887715938209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4688987578628734485003781 879185170992887715938209)
                      ·
                        rfl

theorem cell23_1712207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4, 4].length) (baseStart_1712207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712207 prefixEnd_1712207 := by exact prefixLift 1712207
  have htrace : WordTrace (prefixWord ++ tailWord_1712207) baseStart_1712207 baseEnd_1712207 := by
    simpa [prefixWord, tailWord_1712207, baseEnd_1712207] using wordTrace_append hprefix tailTrace_1712207
  have hstable : (prefixWord ++ tailWord_1712207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712207).length < 2 ^ (prefixWord ++ tailWord_1712207).sum := by decide
  have hdescent : baseEnd_1712207 < baseStart_1712207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712221 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1712221 : Nat := 118140960795 + 1712221 * 2 ^ 59
def prefixEnd_1712221 : Nat := 4983230072969 + 3 ^ 40 * 1712221 * 2
def baseEnd_1712221 : Nat := 293064119907350220387715

theorem tailTrace_1712221 : CollatzResearch.WordTrace tailWord_1712221 prefixEnd_1712221 293064119907350220387715 := by
  unfold tailWord_1712221
  simp only [CollatzResearch.WordTrace]
  refine ⟨62449830329923215910840517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41633220219948810607227011 62449830329923215910840517)
  ·
    refine ⟨11709343186860602983282597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62449830329923215910840517 11709343186860602983282597)
    ·
      refine ⟨2195501847536363059365487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11709343186860602983282597 2195501847536363059365487)
      ·
        refine ⟨3293252771304544589048231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195501847536363059365487 3293252771304544589048231)
        ·
          refine ⟨4939879156956816883572347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293252771304544589048231 4939879156956816883572347)
          ·
            refine ⟨7409818735435225325358521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939879156956816883572347 7409818735435225325358521)
            ·
              refine ⟨5557364051576418994018891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409818735435225325358521 5557364051576418994018891)
              ·
                refine ⟨8336046077364628491028337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557364051576418994018891 8336046077364628491028337)
                ·
                  refine ⟨6252034558023471368271253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336046077364628491028337 6252034558023471368271253)
                  ·
                    refine ⟨293064119907350220387715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6252034558023471368271253 293064119907350220387715)
                    ·
                      rfl

theorem cell23_1712221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1712221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712221 prefixEnd_1712221 := by exact prefixLift 1712221
  have htrace : WordTrace (prefixWord ++ tailWord_1712221) baseStart_1712221 baseEnd_1712221 := by
    simpa [prefixWord, tailWord_1712221, baseEnd_1712221] using wordTrace_append hprefix tailTrace_1712221
  have hstable : (prefixWord ++ tailWord_1712221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712221).length < 2 ^ (prefixWord ++ tailWord_1712221).sum := by decide
  have hdescent : baseEnd_1712221 < baseStart_1712221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712222 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_1712222 : Nat := 118140960795 + 1712222 * 2 ^ 59
def prefixEnd_1712222 : Nat := 4983230072969 + 3 ^ 40 * 1712222 * 2
def baseEnd_1712222 : Nat := 879192873202705157250641

theorem tailTrace_1712222 : CollatzResearch.WordTrace tailWord_1712222 prefixEnd_1712222 879192873202705157250641 := by
  unfold tailWord_1712222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7806233350364949135203365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41633244535279728721084613 7806233350364949135203365)
  ·
    refine ⟨1463668753193427962850631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7806233350364949135203365 1463668753193427962850631)
    ·
      refine ⟨2195503129790141944275947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463668753193427962850631 2195503129790141944275947)
      ·
        refine ⟨3293254694685212916413921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195503129790141944275947 3293254694685212916413921)
        ·
          refine ⟨2469941021013909687310441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293254694685212916413921 2469941021013909687310441)
          ·
            refine ⟨1852455765760432265482831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469941021013909687310441 1852455765760432265482831)
            ·
              refine ⟨2778683648640648398224247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852455765760432265482831 2778683648640648398224247)
              ·
                refine ⟨4168025472960972597336371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778683648640648398224247 4168025472960972597336371)
                ·
                  refine ⟨6252038209441458896004557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168025472960972597336371 6252038209441458896004557)
                  ·
                    refine ⟨2344514328540547086001709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6252038209441458896004557 2344514328540547086001709)
                    ·
                      refine ⟨879192873202705157250641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344514328540547086001709 879192873202705157250641)
                      ·
                        rfl

theorem cell23_1712222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_1712222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712222 prefixEnd_1712222 := by exact prefixLift 1712222
  have htrace : WordTrace (prefixWord ++ tailWord_1712222) baseStart_1712222 baseEnd_1712222 := by
    simpa [prefixWord, tailWord_1712222, baseEnd_1712222] using wordTrace_append hprefix tailTrace_1712222
  have hstable : (prefixWord ++ tailWord_1712222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712222).length < 2 ^ (prefixWord ++ tailWord_1712222).sum := by decide
  have hdescent : baseEnd_1712222 < baseStart_1712222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712224 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1712224 : Nat := 118140960795 + 1712224 * 2 ^ 59
def prefixEnd_1712224 : Nat := 4983230072969 + 3 ^ 40 * 1712224 * 2
def baseEnd_1712224 : Nat := 879193900164014149425631

theorem tailTrace_1712224 : CollatzResearch.WordTrace tailWord_1712224 prefixEnd_1712224 879193900164014149425631 := by
  unfold tailWord_1712224
  simp only [CollatzResearch.WordTrace]
  refine ⟨31224969874456173711599863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41633293165941564948799817 31224969874456173711599863)
  ·
    refine ⟨46837454811684260567399795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31224969874456173711599863 46837454811684260567399795)
    ·
      refine ⟨70256182217526390851099693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46837454811684260567399795 70256182217526390851099693)
      ·
        refine ⟨26346068331572396569162385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70256182217526390851099693 26346068331572396569162385)
        ·
          refine ⟨19759551248679297426871789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26346068331572396569162385 19759551248679297426871789)
          ·
            refine ⟨7409831718254736535076921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19759551248679297426871789 7409831718254736535076921)
            ·
              refine ⟨5557373788691052401307691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7409831718254736535076921 5557373788691052401307691)
              ·
                refine ⟨8336060683036578601961537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557373788691052401307691 8336060683036578601961537)
                ·
                  refine ⟨6252045512277433951471153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8336060683036578601961537 6252045512277433951471153)
                  ·
                    refine ⟨4689034134208075463603365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6252045512277433951471153 4689034134208075463603365)
                    ·
                      refine ⟨879193900164014149425631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4689034134208075463603365 879193900164014149425631)
                      ·
                        rfl

theorem cell23_1712224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1712224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712224 prefixEnd_1712224 := by exact prefixLift 1712224
  have htrace : WordTrace (prefixWord ++ tailWord_1712224) baseStart_1712224 baseEnd_1712224 := by
    simpa [prefixWord, tailWord_1712224, baseEnd_1712224] using wordTrace_append hprefix tailTrace_1712224
  have hstable : (prefixWord ++ tailWord_1712224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712224).length < 2 ^ (prefixWord ++ tailWord_1712224).sum := by decide
  have hdescent : baseEnd_1712224 < baseStart_1712224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712228 : List Nat := [2, 3, 1, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_1712228 : Nat := 118140960795 + 1712228 * 2 ^ 59
def prefixEnd_1712228 : Nat := 4983230072969 + 3 ^ 40 * 1712228 * 2
def baseEnd_1712228 : Nat := 879195954086632133775613

theorem tailTrace_1712228 : CollatzResearch.WordTrace tailWord_1712228 prefixEnd_1712228 879195954086632133775613 := by
  unfold tailWord_1712228
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225042820448928053172669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41633390427265237404230225 31225042820448928053172669)
  ·
    refine ⟨11709391057668348019939751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31225042820448928053172669 11709391057668348019939751)
    ·
      refine ⟨17564086586502522029909627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11709391057668348019939751 17564086586502522029909627)
      ·
        refine ⟨26346129879753783044864441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17564086586502522029909627 26346129879753783044864441)
        ·
          refine ⟨19759597409815337283648331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26346129879753783044864441 19759597409815337283648331)
          ·
            refine ⟨29639396114723005925472497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19759597409815337283648331 29639396114723005925472497)
            ·
              refine ⟨22229547086042254444104373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29639396114723005925472497 22229547086042254444104373)
              ·
                refine ⟨2084020039316461354134785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22229547086042254444104373 2084020039316461354134785)
                ·
                  refine ⟨1563015029487346015601089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084020039316461354134785 1563015029487346015601089)
                  ·
                    refine ⟨1172261272115509511700817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563015029487346015601089 1172261272115509511700817)
                    ·
                      refine ⟨879195954086632133775613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172261272115509511700817 879195954086632133775613)
                      ·
                        rfl

theorem cell23_1712228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_1712228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712228 prefixEnd_1712228 := by exact prefixLift 1712228
  have htrace : WordTrace (prefixWord ++ tailWord_1712228) baseStart_1712228 baseEnd_1712228 := by
    simpa [prefixWord, tailWord_1712228, baseEnd_1712228] using wordTrace_append hprefix tailTrace_1712228
  have hstable : (prefixWord ++ tailWord_1712228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712228).length < 2 ^ (prefixWord ++ tailWord_1712228).sum := by decide
  have hdescent : baseEnd_1712228 < baseStart_1712228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712267 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8]
def baseStart_1712267 : Nat := 118140960795 + 1712267 * 2 ^ 59
def prefixEnd_1712267 : Nat := 4983230072969 + 3 ^ 40 * 1712267 * 2
def baseEnd_1712267 : Nat := 879215979832157481187933

theorem tailTrace_1712267 : CollatzResearch.WordTrace tailWord_1712267 prefixEnd_1712267 879215979832157481187933 := by
  unfold tailWord_1712267
  simp only [CollatzResearch.WordTrace]
  refine ⟨62451508087756565767015055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41634338725171043844676703 62451508087756565767015055)
  ·
    refine ⟨93677262131634848650522583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62451508087756565767015055 93677262131634848650522583)
    ·
      refine ⟨140515893197452272975783875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93677262131634848650522583 140515893197452272975783875)
      ·
        refine ⟨210773839796178409463675813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140515893197452272975783875 210773839796178409463675813)
        ·
          refine ⟨39520094961783451774439215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 210773839796178409463675813 39520094961783451774439215)
          ·
            refine ⟨59280142442675177661658823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39520094961783451774439215 59280142442675177661658823)
            ·
              refine ⟨88920213664012766492488235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59280142442675177661658823 88920213664012766492488235)
              ·
                refine ⟨133380320496019149738732353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88920213664012766492488235 133380320496019149738732353)
                ·
                  refine ⟨100035240372014362304049265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133380320496019149738732353 100035240372014362304049265)
                  ·
                    refine ⟨75026430279010771728036949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 100035240372014362304049265 75026430279010771728036949)
                    ·
                      refine ⟨879215979832157481187933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75026430279010771728036949 879215979832157481187933)
                      ·
                        rfl

theorem cell23_1712267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 8].length) (baseStart_1712267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712267 prefixEnd_1712267 := by exact prefixLift 1712267
  have htrace : WordTrace (prefixWord ++ tailWord_1712267) baseStart_1712267 baseEnd_1712267 := by
    simpa [prefixWord, tailWord_1712267, baseEnd_1712267] using wordTrace_append hprefix tailTrace_1712267
  have hstable : (prefixWord ++ tailWord_1712267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712267).length < 2 ^ (prefixWord ++ tailWord_1712267).sum := by decide
  have hdescent : baseEnd_1712267 < baseStart_1712267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712279 : List Nat := [1, 1, 3, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_1712279 : Nat := 118140960795 + 1712279 * 2 ^ 59
def prefixEnd_1712279 : Nat := 4983230072969 + 3 ^ 40 * 1712279 * 2
def baseEnd_1712279 : Nat := 879222141600011434237879

theorem tailTrace_1712279 : CollatzResearch.WordTrace tailWord_1712279 prefixEnd_1712279 879222141600011434237879 := by
  unfold tailWord_1712279
  simp only [CollatzResearch.WordTrace]
  refine ⟨62451945763713091816451891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41634630509142061210967927 62451945763713091816451891)
  ·
    refine ⟨93677918645569637724677837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62451945763713091816451891 93677918645569637724677837)
    ·
      refine ⟨35129219492088614146754189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93677918645569637724677837 35129219492088614146754189)
      ·
        refine ⟨13173457309533230305032821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35129219492088614146754189 13173457309533230305032821)
        ·
          refine ⟨1235011622768740341096827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13173457309533230305032821 1235011622768740341096827)
          ·
            refine ⟨1852517434153110511645241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235011622768740341096827 1852517434153110511645241)
            ·
              refine ⟨1389388075614832883733931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852517434153110511645241 1389388075614832883733931)
              ·
                refine ⟨2084082113422249325600897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389388075614832883733931 2084082113422249325600897)
                ·
                  refine ⟨1563061585066686994200673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084082113422249325600897 1563061585066686994200673)
                  ·
                    refine ⟨1172296188800015245650505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563061585066686994200673 1172296188800015245650505)
                    ·
                      refine ⟨879222141600011434237879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172296188800015245650505 879222141600011434237879)
                      ·
                        rfl

theorem cell23_1712279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_1712279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712279 prefixEnd_1712279 := by exact prefixLift 1712279
  have htrace : WordTrace (prefixWord ++ tailWord_1712279) baseStart_1712279 baseEnd_1712279 := by
    simpa [prefixWord, tailWord_1712279, baseEnd_1712279] using wordTrace_append hprefix tailTrace_1712279
  have hstable : (prefixWord ++ tailWord_1712279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712279).length < 2 ^ (prefixWord ++ tailWord_1712279).sum := by decide
  have hdescent : baseEnd_1712279 < baseStart_1712279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712361 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 1, 5, 2]
def baseStart_1712361 : Nat := 118140960795 + 1712361 * 2 ^ 59
def prefixEnd_1712361 : Nat := 4983230072969 + 3 ^ 40 * 1712361 * 2
def baseEnd_1712361 : Nat := 879264247013680113412501

theorem tailTrace_1712361 : CollatzResearch.WordTrace tailWord_1712361 prefixEnd_1712361 879264247013680113412501 := by
  unfold tailWord_1712361
  simp only [CollatzResearch.WordTrace]
  refine ⟨62454936549416019820936937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41636624366277346547291291 62454936549416019820936937)
  ·
    refine ⟨46841202412062014865702703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62454936549416019820936937 46841202412062014865702703)
    ·
      refine ⟨70261803618093022298554055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46841202412062014865702703 70261803618093022298554055)
      ·
        refine ⟨105392705427139533447831083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70261803618093022298554055 105392705427139533447831083)
        ·
          refine ⟨158089058140709300171746625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105392705427139533447831083 158089058140709300171746625)
          ·
            refine ⟨118566793605531975128809969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158089058140709300171746625 118566793605531975128809969)
            ·
              refine ⟨88925095204148981346607477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118566793605531975128809969 88925095204148981346607477)
              ·
                refine ⟨8336727675388967001244451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88925095204148981346607477 8336727675388967001244451)
                ·
                  refine ⟨12505091513083450501866677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8336727675388967001244451 12505091513083450501866677)
                  ·
                    refine ⟨1172352329351573484550001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12505091513083450501866677 1172352329351573484550001)
                    ·
                      refine ⟨879264247013680113412501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172352329351573484550001 879264247013680113412501)
                      ·
                        rfl

theorem cell23_1712361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 1, 5, 2].length) (baseStart_1712361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712361 prefixEnd_1712361 := by exact prefixLift 1712361
  have htrace : WordTrace (prefixWord ++ tailWord_1712361) baseStart_1712361 baseEnd_1712361 := by
    simpa [prefixWord, tailWord_1712361, baseEnd_1712361] using wordTrace_append hprefix tailTrace_1712361
  have hstable : (prefixWord ++ tailWord_1712361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712361).length < 2 ^ (prefixWord ++ tailWord_1712361).sum := by decide
  have hdescent : baseEnd_1712361 < baseStart_1712361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712371 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 1, 5]
def baseStart_1712371 : Nat := 118140960795 + 1712371 * 2 ^ 59
def prefixEnd_1712371 : Nat := 4983230072969 + 3 ^ 40 * 1712371 * 2
def baseEnd_1712371 : Nat := 293089793940075024762485

theorem tailTrace_1712371 : CollatzResearch.WordTrace tailWord_1712371 prefixEnd_1712371 293089793940075024762485 := by
  unfold tailWord_1712371
  simp only [CollatzResearch.WordTrace]
  refine ⟨62455301279379791528800967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41636867519586527685867311 62455301279379791528800967)
  ·
    refine ⟨93682951919069687293201451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62455301279379791528800967 93682951919069687293201451)
    ·
      refine ⟨140524427878604530939802177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93682951919069687293201451 140524427878604530939802177)
      ·
        refine ⟨105393320908953398204851633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140524427878604530939802177 105393320908953398204851633)
        ·
          refine ⟨79044990681715048653638725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105393320908953398204851633 79044990681715048653638725)
          ·
            refine ⟨14820935752821571622557261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79044990681715048653638725 14820935752821571622557261)
            ·
              refine ⟨5557850907308089358458973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14820935752821571622557261 5557850907308089358458973)
              ·
                refine ⟨2084194090240533509422115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5557850907308089358458973 2084194090240533509422115)
                ·
                  refine ⟨3126291135360800264133173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084194090240533509422115 3126291135360800264133173)
                  ·
                    refine ⟨293089793940075024762485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3126291135360800264133173 293089793940075024762485)
                    ·
                      rfl

theorem cell23_1712371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 5].length) (baseStart_1712371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712371 prefixEnd_1712371 := by exact prefixLift 1712371
  have htrace : WordTrace (prefixWord ++ tailWord_1712371) baseStart_1712371 baseEnd_1712371 := by
    simpa [prefixWord, tailWord_1712371, baseEnd_1712371] using wordTrace_append hprefix tailTrace_1712371
  have hstable : (prefixWord ++ tailWord_1712371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712371).length < 2 ^ (prefixWord ++ tailWord_1712371).sum := by decide
  have hdescent : baseEnd_1712371 < baseStart_1712371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712384 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_1712384 : Nat := 118140960795 + 1712384 * 2 ^ 59
def prefixEnd_1712384 : Nat := 4983230072969 + 3 ^ 40 * 1712384 * 2
def baseEnd_1712384 : Nat := 293092019022911174474965

theorem tailTrace_1712384 : CollatzResearch.WordTrace tailWord_1712384 prefixEnd_1712384 293092019022911174474965 := by
  unfold tailWord_1712384
  simp only [CollatzResearch.WordTrace]
  refine ⟨31227887714166347374512103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41637183618888463166016137 31227887714166347374512103)
  ·
    refine ⟨46841831571249521061768155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31227887714166347374512103 46841831571249521061768155)
    ·
      refine ⟨70262747356874281592652233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46841831571249521061768155 70262747356874281592652233)
      ·
        refine ⟨52697060517655711194489175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70262747356874281592652233 52697060517655711194489175)
        ·
          refine ⟨79045590776483566791733763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52697060517655711194489175 79045590776483566791733763)
          ·
            refine ⟨118568386164725350187600645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79045590776483566791733763 118568386164725350187600645)
            ·
              refine ⟨22231572405886003160175121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118568386164725350187600645 22231572405886003160175121)
              ·
                refine ⟨16673679304414502370131341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22231572405886003160175121 16673679304414502370131341)
                ·
                  refine ⟨6252629739155438388799253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16673679304414502370131341 6252629739155438388799253)
                  ·
                    refine ⟨293092019022911174474965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6252629739155438388799253 293092019022911174474965)
                    ·
                      rfl

theorem cell23_1712384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_1712384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712384 prefixEnd_1712384 := by exact prefixLift 1712384
  have htrace : WordTrace (prefixWord ++ tailWord_1712384) baseStart_1712384 baseEnd_1712384 := by
    simpa [prefixWord, tailWord_1712384, baseEnd_1712384] using wordTrace_append hprefix tailTrace_1712384
  have hstable : (prefixWord ++ tailWord_1712384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712384).length < 2 ^ (prefixWord ++ tailWord_1712384).sum := by decide
  have hdescent : baseEnd_1712384 < baseStart_1712384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712385 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 1, 1, 3]
def baseStart_1712385 : Nat := 118140960795 + 1712385 * 2 ^ 59
def prefixEnd_1712385 : Nat := 4983230072969 + 3 ^ 40 * 1712385 * 2
def baseEnd_1712385 : Nat := 879276570549388019512391

theorem tailTrace_1712385 : CollatzResearch.WordTrace tailWord_1712385 prefixEnd_1712385 879276570549388019512391 := by
  unfold tailWord_1712385
  simp only [CollatzResearch.WordTrace]
  refine ⟨62455811901329071919810609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41637207934219381279873739 62455811901329071919810609)
  ·
    refine ⟨46841858925996803939857957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62455811901329071919810609 46841858925996803939857957)
    ·
      refine ⟨8782848548624400738723367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46841858925996803939857957 8782848548624400738723367)
      ·
        refine ⟨13174272822936601108085051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8782848548624400738723367 13174272822936601108085051)
        ·
          refine ⟨19761409234404901662127577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174272822936601108085051 19761409234404901662127577)
          ·
            refine ⟨14821056925803676246595683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19761409234404901662127577 14821056925803676246595683)
            ·
              refine ⟨22231585388705514369893525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14821056925803676246595683 22231585388705514369893525)
              ·
                refine ⟨1042105565095570986088759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22231585388705514369893525 1042105565095570986088759)
                ·
                  refine ⟨1563158347643356479133139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042105565095570986088759 1563158347643356479133139)
                  ·
                    refine ⟨2344737521465034718699709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1563158347643356479133139 2344737521465034718699709)
                    ·
                      refine ⟨879276570549388019512391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344737521465034718699709 879276570549388019512391)
                      ·
                        rfl

theorem cell23_1712385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_1712385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712385 prefixEnd_1712385 := by exact prefixLift 1712385
  have htrace : WordTrace (prefixWord ++ tailWord_1712385) baseStart_1712385 baseEnd_1712385 := by
    simpa [prefixWord, tailWord_1712385, baseEnd_1712385] using wordTrace_append hprefix tailTrace_1712385
  have hstable : (prefixWord ++ tailWord_1712385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712385).length < 2 ^ (prefixWord ++ tailWord_1712385).sum := by decide
  have hdescent : baseEnd_1712385 < baseStart_1712385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712401 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 1, 6]
def baseStart_1712401 : Nat := 118140960795 + 1712401 * 2 ^ 59
def prefixEnd_1712401 : Nat := 4983230072969 + 3 ^ 40 * 1712401 * 2
def baseEnd_1712401 : Nat := 293094928746619985637439

theorem tailTrace_1712401 : CollatzResearch.WordTrace tailWord_1712401 prefixEnd_1712401 293094928746619985637439 := by
  unfold tailWord_1712401
  simp only [CollatzResearch.WordTrace]
  refine ⟨62456395469271106652393057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41637596979514071101595371 62456395469271106652393057)
  ·
    refine ⟨46842296601953329989294793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62456395469271106652393057 46842296601953329989294793)
    ·
      refine ⟨35131722451464997491971095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46842296601953329989294793 35131722451464997491971095)
      ·
        refine ⟨52697583677197496237956643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35131722451464997491971095 52697583677197496237956643)
        ·
          refine ⟨79046375515796244356934965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52697583677197496237956643 79046375515796244356934965)
          ·
            refine ⟨7410597704605897908462653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79046375515796244356934965 7410597704605897908462653)
            ·
              refine ⟨2778974139227211715673495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410597704605897908462653 2778974139227211715673495)
              ·
                refine ⟨4168461208840817573510243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778974139227211715673495 4168461208840817573510243)
                ·
                  refine ⟨6252691813261226360265365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4168461208840817573510243 6252691813261226360265365)
                  ·
                    refine ⟨293094928746619985637439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6252691813261226360265365 293094928746619985637439)
                    ·
                      rfl

theorem cell23_1712401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_1712401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712401 prefixEnd_1712401 := by exact prefixLift 1712401
  have htrace : WordTrace (prefixWord ++ tailWord_1712401) baseStart_1712401 baseEnd_1712401 := by
    simpa [prefixWord, tailWord_1712401, baseEnd_1712401] using wordTrace_append hprefix tailTrace_1712401
  have hstable : (prefixWord ++ tailWord_1712401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712401).length < 2 ^ (prefixWord ++ tailWord_1712401).sum := by decide
  have hdescent : baseEnd_1712401 < baseStart_1712401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712408 : List Nat := [2, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1712408 : Nat := 118140960795 + 1712408 * 2 ^ 59
def prefixEnd_1712408 : Nat := 4983230072969 + 3 ^ 40 * 1712408 * 2
def baseEnd_1712408 : Nat := 879288380604441429524785

theorem tailTrace_1712408 : CollatzResearch.WordTrace tailWord_1712408 prefixEnd_1712408 879288380604441429524785 := by
  unfold tailWord_1712408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228325390122873423948939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41637767186830497898598585 31228325390122873423948939)
  ·
    refine ⟨46842488085184310135923409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31228325390122873423948939 46842488085184310135923409)
    ·
      refine ⟨35131866063888232601942557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46842488085184310135923409 35131866063888232601942557)
      ·
        refine ⟨13174449773958087225728459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35131866063888232601942557 13174449773958087225728459)
        ·
          refine ⟨19761674660937130838592689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174449773958087225728459 19761674660937130838592689)
          ·
            refine ⟨14821255995702848128944517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19761674660937130838592689 14821255995702848128944517)
            ·
              refine ⟨2778985499194284024177097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14821255995702848128944517 2778985499194284024177097)
              ·
                refine ⟨2084239124395713018132823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778985499194284024177097 2084239124395713018132823)
                ·
                  refine ⟨3126358686593569527199235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084239124395713018132823 3126358686593569527199235)
                  ·
                    refine ⟨4689538029890354290798853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3126358686593569527199235 4689538029890354290798853)
                    ·
                      refine ⟨879288380604441429524785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4689538029890354290798853 879288380604441429524785)
                      ·
                        rfl

theorem cell23_1712408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1712408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712408 prefixEnd_1712408 := by exact prefixLift 1712408
  have htrace : WordTrace (prefixWord ++ tailWord_1712408) baseStart_1712408 baseEnd_1712408 := by
    simpa [prefixWord, tailWord_1712408, baseEnd_1712408] using wordTrace_append hprefix tailTrace_1712408
  have hstable : (prefixWord ++ tailWord_1712408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712408).length < 2 ^ (prefixWord ++ tailWord_1712408).sum := by decide
  have hdescent : baseEnd_1712408 < baseStart_1712408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712411 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3]
def baseStart_1712411 : Nat := 118140960795 + 1712411 * 2 ^ 59
def prefixEnd_1712411 : Nat := 4983230072969 + 3 ^ 40 * 1712411 * 2
def baseEnd_1712411 : Nat := 879289921046404917787271

theorem tailTrace_1712411 : CollatzResearch.WordTrace tailWord_1712411 prefixEnd_1712411 879289921046404917787271 := by
  unfold tailWord_1712411
  simp only [CollatzResearch.WordTrace]
  refine ⟨62456760199234878360257087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41637840132823252240171391 62456760199234878360257087)
  ·
    refine ⟨93685140298852317540385631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62456760199234878360257087 93685140298852317540385631)
    ·
      refine ⟨140527710448278476310578447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93685140298852317540385631 140527710448278476310578447)
      ·
        refine ⟨210791565672417714465867671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140527710448278476310578447 210791565672417714465867671)
        ·
          refine ⟨316187348508626571698801507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210791565672417714465867671 316187348508626571698801507)
          ·
            refine ⟨474281022762939857548202261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316187348508626571698801507 474281022762939857548202261)
            ·
              refine ⟨22231922942012805822571981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 474281022762939857548202261 22231922942012805822571981)
              ·
                refine ⟨8336971103254802183464493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22231922942012805822571981 8336971103254802183464493)
                ·
                  refine ⟨3126364163720550818799185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8336971103254802183464493 3126364163720550818799185)
                  ·
                    refine ⟨2344773122790413114099389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126364163720550818799185 2344773122790413114099389)
                    ·
                      refine ⟨879289921046404917787271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344773122790413114099389 879289921046404917787271)
                      ·
                        rfl

theorem cell23_1712411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 2, 3].length) (baseStart_1712411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712411 prefixEnd_1712411 := by exact prefixLift 1712411
  have htrace : WordTrace (prefixWord ++ tailWord_1712411) baseStart_1712411 baseEnd_1712411 := by
    simpa [prefixWord, tailWord_1712411, baseEnd_1712411] using wordTrace_append hprefix tailTrace_1712411
  have hstable : (prefixWord ++ tailWord_1712411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712411).length < 2 ^ (prefixWord ++ tailWord_1712411).sum := by decide
  have hdescent : baseEnd_1712411 < baseStart_1712411 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712418 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1712418 : Nat := 118140960795 + 1712418 * 2 ^ 59
def prefixEnd_1712418 : Nat := 4983230072969 + 3 ^ 40 * 1712418 * 2
def baseEnd_1712418 : Nat := 293097838470328796799913

theorem tailTrace_1712418 : CollatzResearch.WordTrace tailWord_1712418 prefixEnd_1712418 293097838470328796799913 := by
  unfold tailWord_1712418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614253877552379638940477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41638010340139679037174605 15614253877552379638940477)
  ·
    refine ⟨5855345204082142364602679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15614253877552379638940477 5855345204082142364602679)
    ·
      refine ⟨8783017806123213546904019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855345204082142364602679 8783017806123213546904019)
      ·
        refine ⟨13174526709184820320356029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8783017806123213546904019 13174526709184820320356029)
        ·
          refine ⟨4940447515944307620133511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13174526709184820320356029 4940447515944307620133511)
          ·
            refine ⟨7410671273916461430200267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940447515944307620133511 7410671273916461430200267)
            ·
              refine ⟨11116006910874692145300401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7410671273916461430200267 11116006910874692145300401)
              ·
                refine ⟨8337005183156019108975301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116006910874692145300401 8337005183156019108975301)
                ·
                  refine ⟨1563188471841753582932869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8337005183156019108975301 1563188471841753582932869)
                  ·
                    refine ⟨293097838470328796799913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563188471841753582932869 293097838470328796799913)
                    ·
                      rfl

theorem cell23_1712418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1712418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712418 prefixEnd_1712418 := by exact prefixLift 1712418
  have htrace : WordTrace (prefixWord ++ tailWord_1712418) baseStart_1712418 baseEnd_1712418 := by
    simpa [prefixWord, tailWord_1712418, baseEnd_1712418] using wordTrace_append hprefix tailTrace_1712418
  have hstable : (prefixWord ++ tailWord_1712418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712418).length < 2 ^ (prefixWord ++ tailWord_1712418).sum := by decide
  have hdescent : baseEnd_1712418 < baseStart_1712418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712428 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_1712428 : Nat := 118140960795 + 1712428 * 2 ^ 59
def prefixEnd_1712428 : Nat := 4983230072969 + 3 ^ 40 * 1712428 * 2
def baseEnd_1712428 : Nat := 879298650217531351274693

theorem tailTrace_1712428 : CollatzResearch.WordTrace tailWord_1712428 prefixEnd_1712428 879298650217531351274693 := by
  unfold tailWord_1712428
  simp only [CollatzResearch.WordTrace]
  refine ⟨31228690120086645131812969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41638253493448860175750625 31228690120086645131812969)
  ·
    refine ⟨23421517590064983848859727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31228690120086645131812969 23421517590064983848859727)
    ·
      refine ⟨35132276385097475773289591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23421517590064983848859727 35132276385097475773289591)
      ·
        refine ⟨52698414577646213659934387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35132276385097475773289591 52698414577646213659934387)
        ·
          refine ⟨79047621866469320489901581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52698414577646213659934387 79047621866469320489901581)
          ·
            refine ⟨29642858199925995183713093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79047621866469320489901581 29642858199925995183713093)
            ·
              refine ⟨5558035912486124096946205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29642858199925995183713093 5558035912486124096946205)
              ·
                refine ⟨2084263467182296536354827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558035912486124096946205 2084263467182296536354827)
                ·
                  refine ⟨3126395200773444804532241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084263467182296536354827 3126395200773444804532241)
                  ·
                    refine ⟨2344796400580083603399181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126395200773444804532241 2344796400580083603399181)
                    ·
                      refine ⟨879298650217531351274693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344796400580083603399181 879298650217531351274693)
                      ·
                        rfl

theorem cell23_1712428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_1712428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712428 prefixEnd_1712428 := by exact prefixLift 1712428
  have htrace : WordTrace (prefixWord ++ tailWord_1712428) baseStart_1712428 baseEnd_1712428 := by
    simpa [prefixWord, tailWord_1712428, baseEnd_1712428] using wordTrace_append hprefix tailTrace_1712428
  have hstable : (prefixWord ++ tailWord_1712428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712428).length < 2 ^ (prefixWord ++ tailWord_1712428).sum := by decide
  have hdescent : baseEnd_1712428 < baseStart_1712428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712442 : List Nat := [3, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2]
def baseStart_1712442 : Nat := 118140960795 + 1712442 * 2 ^ 59
def prefixEnd_1712442 : Nat := 4983230072969 + 3 ^ 40 * 1712442 * 2
def baseEnd_1712442 : Nat := 879305838946694296499629

theorem tailTrace_1712442 : CollatzResearch.WordTrace tailWord_1712442 prefixEnd_1712442 879305838946694296499629 := by
  unfold tailWord_1712442
  simp only [CollatzResearch.WordTrace]
  refine ⟨15614472715530642663658895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41638593908081713769757053 15614472715530642663658895)
  ·
    refine ⟨23421709073295963995488343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15614472715530642663658895 23421709073295963995488343)
    ·
      refine ⟨35132563609943945993232515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23421709073295963995488343 35132563609943945993232515)
      ·
        refine ⟨52698845414915918989848773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35132563609943945993232515 52698845414915918989848773)
        ·
          refine ⟨9881033515296734810596645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52698845414915918989848773 9881033515296734810596645)
          ·
            refine ⟨1852693784118137776986871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9881033515296734810596645 1852693784118137776986871)
            ·
              refine ⟨2779040676177206665480307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852693784118137776986871 2779040676177206665480307)
              ·
                refine ⟨4168561014265809998220461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779040676177206665480307 4168561014265809998220461)
                ·
                  refine ⟨1563210380349678749332673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4168561014265809998220461 1563210380349678749332673)
                  ·
                    refine ⟨1172407785262259061999505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563210380349678749332673 1172407785262259061999505)
                    ·
                      refine ⟨879305838946694296499629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172407785262259061999505 879305838946694296499629)
                      ·
                        rfl

theorem cell23_1712442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_1712442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712442 prefixEnd_1712442 := by exact prefixLift 1712442
  have htrace : WordTrace (prefixWord ++ tailWord_1712442) baseStart_1712442 baseEnd_1712442 := by
    simpa [prefixWord, tailWord_1712442, baseEnd_1712442] using wordTrace_append hprefix tailTrace_1712442
  have hstable : (prefixWord ++ tailWord_1712442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712442).length < 2 ^ (prefixWord ++ tailWord_1712442).sum := by decide
  have hdescent : baseEnd_1712442 < baseStart_1712442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712452 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1712452 : Nat := 118140960795 + 1712452 * 2 ^ 59
def prefixEnd_1712452 : Nat := 4983230072969 + 3 ^ 40 * 1712452 * 2
def baseEnd_1712452 : Nat := 293103657917746419124861

theorem tailTrace_1712452 : CollatzResearch.WordTrace tailWord_1712452 prefixEnd_1712452 293103657917746419124861 := by
  unfold tailWord_1712452
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229127796043171181249805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41638837061390894908333073 31229127796043171181249805)
  ·
    refine ⟨11710922923516189192968677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31229127796043171181249805 11710922923516189192968677)
    ·
      refine ⟨2195798048159285473681627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11710922923516189192968677 2195798048159285473681627)
      ·
        refine ⟨3293697072238928210522441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195798048159285473681627 3293697072238928210522441)
        ·
          refine ⟨2470272804179196157891831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293697072238928210522441 2470272804179196157891831)
          ·
            refine ⟨3705409206268794236837747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470272804179196157891831 3705409206268794236837747)
            ·
              refine ⟨5558113809403191355256621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705409206268794236837747 5558113809403191355256621)
              ·
                refine ⟨2084292678526196758221233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5558113809403191355256621 2084292678526196758221233)
                ·
                  refine ⟨1563219508894647568665925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084292678526196758221233 1563219508894647568665925)
                  ·
                    refine ⟨293103657917746419124861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563219508894647568665925 293103657917746419124861)
                    ·
                      rfl

theorem cell23_1712452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1712452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712452 prefixEnd_1712452 := by exact prefixLift 1712452
  have htrace : WordTrace (prefixWord ++ tailWord_1712452) baseStart_1712452 baseEnd_1712452 := by
    simpa [prefixWord, tailWord_1712452, baseEnd_1712452] using wordTrace_append hprefix tailTrace_1712452
  have hstable : (prefixWord ++ tailWord_1712452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712452).length < 2 ^ (prefixWord ++ tailWord_1712452).sum := by decide
  have hdescent : baseEnd_1712452 < baseStart_1712452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712492 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_1712492 : Nat := 118140960795 + 1712492 * 2 ^ 59
def prefixEnd_1712492 : Nat := 4983230072969 + 3 ^ 40 * 1712492 * 2
def baseEnd_1712492 : Nat := 879331512979419100874399

theorem tailTrace_1712492 : CollatzResearch.WordTrace tailWord_1712492 prefixEnd_1712492 879331512979419100874399 := by
  unfold tailWord_1712492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229857255970714596977865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41639809674627619462637153 31229857255970714596977865)
  ·
    refine ⟨23422392941978035947733399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31229857255970714596977865 23422392941978035947733399)
    ·
      refine ⟨35133589412967053921600099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23422392941978035947733399 35133589412967053921600099)
      ·
        refine ⟨52700384119450580882400149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35133589412967053921600099 52700384119450580882400149)
        ·
          refine ⟨2470330505599245978862507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52700384119450580882400149 2470330505599245978862507)
          ·
            refine ⟨3705495758398868968293761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470330505599245978862507 3705495758398868968293761)
            ·
              refine ⟨2779121818799151726220321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3705495758398868968293761 2779121818799151726220321)
              ·
                refine ⟨2084341364099363794665241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779121818799151726220321 2084341364099363794665241)
                ·
                  refine ⟨1563256023074522845998931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084341364099363794665241 1563256023074522845998931)
                  ·
                    refine ⟨2344884034611784268998397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1563256023074522845998931 2344884034611784268998397)
                    ·
                      refine ⟨879331512979419100874399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344884034611784268998397 879331512979419100874399)
                      ·
                        rfl

theorem cell23_1712492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_1712492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712492 prefixEnd_1712492 := by exact prefixLift 1712492
  have htrace : WordTrace (prefixWord ++ tailWord_1712492) baseStart_1712492 baseEnd_1712492 := by
    simpa [prefixWord, tailWord_1712492, baseEnd_1712492] using wordTrace_append hprefix tailTrace_1712492
  have hstable : (prefixWord ++ tailWord_1712492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712492).length < 2 ^ (prefixWord ++ tailWord_1712492).sum := by decide
  have hdescent : baseEnd_1712492 < baseStart_1712492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712511 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4]
def baseStart_1712511 : Nat := 118140960795 + 1712511 * 2 ^ 59
def prefixEnd_1712511 : Nat := 4983230072969 + 3 ^ 40 * 1712511 * 2
def baseEnd_1712511 : Nat := 879341269111854526536811

theorem tailTrace_1712511 : CollatzResearch.WordTrace tailWord_1712511 prefixEnd_1712511 879341269111854526536811 := by
  unfold tailWord_1712511
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460407498872595438897387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41640271665915063625931591 62460407498872595438897387)
  ·
    refine ⟨93690611248308893158346081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62460407498872595438897387 93690611248308893158346081)
    ·
      refine ⟨70267958436231669868759561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93690611248308893158346081 70267958436231669868759561)
      ·
        refine ⟨52700968827173752401569671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70267958436231669868759561 52700968827173752401569671)
        ·
          refine ⟨79051453240760628602354507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52700968827173752401569671 79051453240760628602354507)
          ·
            refine ⟨118577179861140942903531761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79051453240760628602354507 118577179861140942903531761)
            ·
              refine ⟨88932884895855707177648821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118577179861140942903531761 88932884895855707177648821)
              ·
                refine ⟨8337457958986472547904577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88932884895855707177648821 8337457958986472547904577)
                ·
                  refine ⟨6253093469239854410928433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337457958986472547904577 6253093469239854410928433)
                  ·
                    refine ⟨4689820101929890808196325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6253093469239854410928433 4689820101929890808196325)
                    ·
                      refine ⟨879341269111854526536811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4689820101929890808196325 879341269111854526536811)
                      ·
                        rfl

theorem cell23_1712511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_1712511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712511 prefixEnd_1712511 := by exact prefixLift 1712511
  have htrace : WordTrace (prefixWord ++ tailWord_1712511) baseStart_1712511 baseEnd_1712511 := by
    simpa [prefixWord, tailWord_1712511, baseEnd_1712511] using wordTrace_append hprefix tailTrace_1712511
  have hstable : (prefixWord ++ tailWord_1712511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712511).length < 2 ^ (prefixWord ++ tailWord_1712511).sum := by decide
  have hdescent : baseEnd_1712511 < baseStart_1712511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712521 : List Nat := [1, 2, 1, 1, 6, 1, 1, 1, 9]
def baseStart_1712521 : Nat := 118140960795 + 1712521 * 2 ^ 59
def prefixEnd_1712521 : Nat := 4983230072969 + 3 ^ 40 * 1712521 * 2
def baseEnd_1712521 : Nat := 97705155990933276379085

theorem tailTrace_1712521 : CollatzResearch.WordTrace tailWord_1712521 prefixEnd_1712521 97705155990933276379085 := by
  unfold tailWord_1712521
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460772228836367146761417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41640514819224244764507611 62460772228836367146761417)
  ·
    refine ⟨46845579171627275360071063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62460772228836367146761417 46845579171627275360071063)
    ·
      refine ⟨70268368757440913040106595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46845579171627275360071063 70268368757440913040106595)
      ·
        refine ⟨105402553136161369560159893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70268368757440913040106595 105402553136161369560159893)
        ·
          refine ⟨4940744678257564198132495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105402553136161369560159893 4940744678257564198132495)
          ·
            refine ⟨7411117017386346297198743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940744678257564198132495 7411117017386346297198743)
            ·
              refine ⟨11116675526079519445798115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7411117017386346297198743 11116675526079519445798115)
              ·
                refine ⟨16675013289119279168697173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11116675526079519445798115 16675013289119279168697173)
                ·
                  refine ⟨97705155990933276379085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16675013289119279168697173 97705155990933276379085)
                  ·
                    rfl

theorem cell23_1712521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 1, 9].length) (baseStart_1712521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712521 prefixEnd_1712521 := by exact prefixLift 1712521
  have htrace : WordTrace (prefixWord ++ tailWord_1712521) baseStart_1712521 baseEnd_1712521 := by
    simpa [prefixWord, tailWord_1712521, baseEnd_1712521] using wordTrace_append hprefix tailTrace_1712521
  have hstable : (prefixWord ++ tailWord_1712521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712521).length < 2 ^ (prefixWord ++ tailWord_1712521).sum := by decide
  have hdescent : baseEnd_1712521 < baseStart_1712521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712548 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_1712548 : Nat := 118140960795 + 1712548 * 2 ^ 59
def prefixEnd_1712548 : Nat := 4983230072969 + 3 ^ 40 * 1712548 * 2
def baseEnd_1712548 : Nat := 879360267896070881774141

theorem tailTrace_1712548 : CollatzResearch.WordTrace tailWord_1712548 prefixEnd_1712548 879360267896070881774141 := by
  unfold tailWord_1712548
  simp only [CollatzResearch.WordTrace]
  refine ⟨31230878499869275378997149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41641171333159033838662865 31230878499869275378997149)
  ·
    refine ⟨11711579437450978267123931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31230878499869275378997149 11711579437450978267123931)
    ·
      refine ⟨17567369156176467400685897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711579437450978267123931 17567369156176467400685897)
      ·
        refine ⟨13175526867132350550514423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17567369156176467400685897 13175526867132350550514423)
        ·
          refine ⟨19763290300698525825771635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13175526867132350550514423 19763290300698525825771635)
          ·
            refine ⟨29644935451047788738657453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19763290300698525825771635 29644935451047788738657453)
            ·
              refine ⟨11116850794142920776996545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29644935451047788738657453 11116850794142920776996545)
              ·
                refine ⟨8337638095607190582747409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11116850794142920776996545 8337638095607190582747409)
                ·
                  refine ⟨6253228571705392937060557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337638095607190582747409 6253228571705392937060557)
                  ·
                    refine ⟨2344960714389522351397709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6253228571705392937060557 2344960714389522351397709)
                    ·
                      refine ⟨879360267896070881774141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2344960714389522351397709 879360267896070881774141)
                      ·
                        rfl

theorem cell23_1712548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_1712548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712548 prefixEnd_1712548 := by exact prefixLift 1712548
  have htrace : WordTrace (prefixWord ++ tailWord_1712548) baseStart_1712548 baseEnd_1712548 := by
    simpa [prefixWord, tailWord_1712548, baseEnd_1712548] using wordTrace_append hprefix tailTrace_1712548
  have hstable : (prefixWord ++ tailWord_1712548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712548).length < 2 ^ (prefixWord ++ tailWord_1712548).sum := by decide
  have hdescent : baseEnd_1712548 < baseStart_1712548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712591 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5]
def baseStart_1712591 : Nat := 118140960795 + 1712591 * 2 ^ 59
def prefixEnd_1712591 : Nat := 4983230072969 + 3 ^ 40 * 1712591 * 2
def baseEnd_1712591 : Nat := 879382347564214213536443

theorem tailTrace_1712591 : CollatzResearch.WordTrace tailWord_1712591 prefixEnd_1712591 879382347564214213536443 := by
  unfold tailWord_1712591
  simp only [CollatzResearch.WordTrace]
  refine ⟨62463325338582769101809627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41642216892388512734539751 62463325338582769101809627)
  ·
    refine ⟨93694988007874153652714441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62463325338582769101809627 93694988007874153652714441)
    ·
      refine ⟨70271241005905615239535831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93694988007874153652714441 70271241005905615239535831)
      ·
        refine ⟨105406861508858422859303747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70271241005905615239535831 105406861508858422859303747)
        ·
          refine ⟨158110292263287634288955621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105406861508858422859303747 158110292263287634288955621)
          ·
            refine ⟨29645679799366431429179179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158110292263287634288955621 29645679799366431429179179)
            ·
              refine ⟨44468519699049647143768769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29645679799366431429179179 44468519699049647143768769)
              ·
                refine ⟨33351389774287235357826577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44468519699049647143768769 33351389774287235357826577)
                ·
                  refine ⟨25013542330715426518369933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33351389774287235357826577 25013542330715426518369933)
                  ·
                    refine ⟨9380078374018284944388725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25013542330715426518369933 9380078374018284944388725)
                    ·
                      refine ⟨879382347564214213536443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9380078374018284944388725 879382347564214213536443)
                      ·
                        rfl

theorem cell23_1712591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 5].length) (baseStart_1712591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712591 prefixEnd_1712591 := by exact prefixLift 1712591
  have htrace : WordTrace (prefixWord ++ tailWord_1712591) baseStart_1712591 baseEnd_1712591 := by
    simpa [prefixWord, tailWord_1712591, baseEnd_1712591] using wordTrace_append hprefix tailTrace_1712591
  have hstable : (prefixWord ++ tailWord_1712591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712591).length < 2 ^ (prefixWord ++ tailWord_1712591).sum := by decide
  have hdescent : baseEnd_1712591 < baseStart_1712591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712605 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_1712605 : Nat := 118140960795 + 1712605 * 2 ^ 59
def prefixEnd_1712605 : Nat := 4983230072969 + 3 ^ 40 * 1712605 * 2
def baseEnd_1712605 : Nat := 879389536293377158761379

theorem tailTrace_1712605 : CollatzResearch.WordTrace tailWord_1712605 prefixEnd_1712605 879389536293377158761379 := by
  unfold tailWord_1712605
  simp only [CollatzResearch.WordTrace]
  refine ⟨62463835960532049492819269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41642557307021366328546179 62463835960532049492819269)
  ·
    refine ⟨11711969242599759279903613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62463835960532049492819269 11711969242599759279903613)
    ·
      refine ⟨4391988465974909729963855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11711969242599759279903613 4391988465974909729963855)
      ·
        refine ⟨6587982698962364594945783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4391988465974909729963855 6587982698962364594945783)
        ·
          refine ⟨9881974048443546892418675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6587982698962364594945783 9881974048443546892418675)
          ·
            refine ⟨14822961072665320338628013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9881974048443546892418675 14822961072665320338628013)
            ·
              refine ⟨5558610402249495126985505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14822961072665320338628013 5558610402249495126985505)
              ·
                refine ⟨4168957801687121345239129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558610402249495126985505 4168957801687121345239129)
                ·
                  refine ⟨3126718351265341008929347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168957801687121345239129 3126718351265341008929347)
                  ·
                    refine ⟨4690077526898011513394021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3126718351265341008929347 4690077526898011513394021)
                    ·
                      refine ⟨879389536293377158761379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4690077526898011513394021 879389536293377158761379)
                      ·
                        rfl

theorem cell23_1712605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_1712605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712605 prefixEnd_1712605 := by exact prefixLift 1712605
  have htrace : WordTrace (prefixWord ++ tailWord_1712605) baseStart_1712605 baseEnd_1712605 := by
    simpa [prefixWord, tailWord_1712605, baseEnd_1712605] using wordTrace_append hprefix tailTrace_1712605
  have hstable : (prefixWord ++ tailWord_1712605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712605).length < 2 ^ (prefixWord ++ tailWord_1712605).sum := by decide
  have hdescent : baseEnd_1712605 < baseStart_1712605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712631 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1712631 : Nat := 118140960795 + 1712631 * 2 ^ 59
def prefixEnd_1712631 : Nat := 4983230072969 + 3 ^ 40 * 1712631 * 2
def baseEnd_1712631 : Nat := 879402886790394057036259

theorem tailTrace_1712631 : CollatzResearch.WordTrace tailWord_1712631 prefixEnd_1712631 879402886790394057036259 := by
  unfold tailWord_1712631
  simp only [CollatzResearch.WordTrace]
  refine ⟨62464784258437855933265747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41643189505625237288843831 62464784258437855933265747)
  ·
    refine ⟨93697176387656783899898621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62464784258437855933265747 93697176387656783899898621)
    ·
      refine ⟨35136441145371293962461983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93697176387656783899898621 35136441145371293962461983)
      ·
        refine ⟨52704661718056940943692975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35136441145371293962461983 52704661718056940943692975)
        ·
          refine ⟨79056992577085411415539463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52704661718056940943692975 79056992577085411415539463)
          ·
            refine ⟨118585488865628117123309195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79056992577085411415539463 118585488865628117123309195)
            ·
              refine ⟨177878233298442175684963793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118585488865628117123309195 177878233298442175684963793)
              ·
                refine ⟨133408674973831631763722845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177878233298442175684963793 133408674973831631763722845)
                ·
                  refine ⟨50028253115186861911396067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133408674973831631763722845 50028253115186861911396067)
                  ·
                    refine ⟨75042379672780292867094101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50028253115186861911396067 75042379672780292867094101)
                    ·
                      refine ⟨879402886790394057036259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 75042379672780292867094101 879402886790394057036259)
                      ·
                        rfl

theorem cell23_1712631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1712631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712631 prefixEnd_1712631 := by exact prefixLift 1712631
  have htrace : WordTrace (prefixWord ++ tailWord_1712631) baseStart_1712631 baseEnd_1712631 := by
    simpa [prefixWord, tailWord_1712631, baseEnd_1712631] using wordTrace_append hprefix tailTrace_1712631
  have hstable : (prefixWord ++ tailWord_1712631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712631).length < 2 ^ (prefixWord ++ tailWord_1712631).sum := by decide
  have hdescent : baseEnd_1712631 < baseStart_1712631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712688 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_1712688 : Nat := 118140960795 + 1712688 * 2 ^ 59
def prefixEnd_1712688 : Nat := 4983230072969 + 3 ^ 40 * 1712688 * 2
def baseEnd_1712688 : Nat := 293144051729233444674499

theorem tailTrace_1712688 : CollatzResearch.WordTrace tailWord_1712688 prefixEnd_1712688 293144051729233444674499 := by
  unfold tailWord_1712688
  simp only [CollatzResearch.WordTrace]
  refine ⟨31233431609615677334045359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41644575479487569778727145 31233431609615677334045359)
  ·
    refine ⟨46850147414423516001068039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31233431609615677334045359 46850147414423516001068039)
    ·
      refine ⟨70275221121635274001602059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46850147414423516001068039 70275221121635274001602059)
      ·
        refine ⟨105412831682452911002403089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70275221121635274001602059 105412831682452911002403089)
        ·
          refine ⟨79059623761839683251802317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105412831682452911002403089 79059623761839683251802317)
          ·
            refine ⟨29647358910689881219425869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79059623761839683251802317 29647358910689881219425869)
            ·
              refine ⟨11117759591508705457284701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29647358910689881219425869 11117759591508705457284701)
              ·
                refine ⟨4169159846815764546481763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11117759591508705457284701 4169159846815764546481763)
                ·
                  refine ⟨6253739770223646819722645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169159846815764546481763 6253739770223646819722645)
                  ·
                    refine ⟨293144051729233444674499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6253739770223646819722645 293144051729233444674499)
                    ·
                      rfl

theorem cell23_1712688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_1712688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712688 prefixEnd_1712688 := by exact prefixLift 1712688
  have htrace : WordTrace (prefixWord ++ tailWord_1712688) baseStart_1712688 baseEnd_1712688 := by
    simpa [prefixWord, tailWord_1712688, baseEnd_1712688] using wordTrace_append hprefix tailTrace_1712688
  have hstable : (prefixWord ++ tailWord_1712688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712688).length < 2 ^ (prefixWord ++ tailWord_1712688).sum := by decide
  have hdescent : baseEnd_1712688 < baseStart_1712688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712695 : List Nat := [1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_1712695 : Nat := 118140960795 + 1712695 * 2 ^ 59
def prefixEnd_1712695 : Nat := 4983230072969 + 3 ^ 40 * 1712695 * 2
def baseEnd_1712695 : Nat := 879435749552281806635965

theorem tailTrace_1712695 : CollatzResearch.WordTrace tailWord_1712695 prefixEnd_1712695 879435749552281806635965 := by
  unfold tailWord_1712695
  simp only [CollatzResearch.WordTrace]
  refine ⟨62467118530205994863595539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41644745686803996575730359 62467118530205994863595539)
  ·
    refine ⟨93700677795308992295393309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62467118530205994863595539 93700677795308992295393309)
    ·
      refine ⟨35137754173240872110772491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93700677795308992295393309 35137754173240872110772491)
      ·
        refine ⟨52706631259861308166158737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35137754173240872110772491 52706631259861308166158737)
        ·
          refine ⟨39529973444895981124619053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52706631259861308166158737 39529973444895981124619053)
          ·
            refine ⟨14823740041835992921732145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39529973444895981124619053 14823740041835992921732145)
            ·
              refine ⟨11117805031376994691299109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14823740041835992921732145 11117805031376994691299109)
              ·
                refine ⟨2084588443383186504618583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11117805031376994691299109 2084588443383186504618583)
                ·
                  refine ⟨3126882665074779756927875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084588443383186504618583 3126882665074779756927875)
                  ·
                    refine ⟨4690323997612169635391813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3126882665074779756927875 4690323997612169635391813)
                    ·
                      refine ⟨879435749552281806635965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4690323997612169635391813 879435749552281806635965)
                      ·
                        rfl

theorem cell23_1712695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_1712695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712695 prefixEnd_1712695 := by exact prefixLift 1712695
  have htrace : WordTrace (prefixWord ++ tailWord_1712695) baseStart_1712695 baseEnd_1712695 := by
    simpa [prefixWord, tailWord_1712695, baseEnd_1712695] using wordTrace_append hprefix tailTrace_1712695
  have hstable : (prefixWord ++ tailWord_1712695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712695).length < 2 ^ (prefixWord ++ tailWord_1712695).sum := by decide
  have hdescent : baseEnd_1712695 < baseStart_1712695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712705 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 1, 6]
def baseStart_1712705 : Nat := 118140960795 + 1712705 * 2 ^ 59
def prefixEnd_1712705 : Nat := 4983230072969 + 3 ^ 40 * 1712705 * 2
def baseEnd_1712705 : Nat := 293146961452942255836973

theorem tailTrace_1712705 : CollatzResearch.WordTrace tailWord_1712705 prefixEnd_1712705 293146961452942255836973 := by
  unfold tailWord_1712705
  simp only [CollatzResearch.WordTrace]
  refine ⟨62467483260169766571459569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41644988840113177714306379 62467483260169766571459569)
  ·
    refine ⟨46850612445127324928594677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62467483260169766571459569 46850612445127324928594677)
    ·
      refine ⟨4392244916730686712055751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46850612445127324928594677 4392244916730686712055751)
      ·
        refine ⟨6588367375096030068083627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392244916730686712055751 6588367375096030068083627)
        ·
          refine ⟨9882551062644045102125441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588367375096030068083627 9882551062644045102125441)
          ·
            refine ⟨7411913296983033826594081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9882551062644045102125441 7411913296983033826594081)
            ·
              refine ⟨5558934972737275369945561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7411913296983033826594081 5558934972737275369945561)
              ·
                refine ⟨4169201229552956527459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558934972737275369945561 4169201229552956527459171)
                ·
                  refine ⟨6253801844329434791188757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169201229552956527459171 6253801844329434791188757)
                  ·
                    refine ⟨293146961452942255836973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6253801844329434791188757 293146961452942255836973)
                    ·
                      rfl

theorem cell23_1712705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_1712705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712705 prefixEnd_1712705 := by exact prefixLift 1712705
  have htrace : WordTrace (prefixWord ++ tailWord_1712705) baseStart_1712705 baseEnd_1712705 := by
    simpa [prefixWord, tailWord_1712705, baseEnd_1712705] using wordTrace_append hprefix tailTrace_1712705
  have hstable : (prefixWord ++ tailWord_1712705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712705).length < 2 ^ (prefixWord ++ tailWord_1712705).sum := by decide
  have hdescent : baseEnd_1712705 < baseStart_1712705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712732 : List Nat := [2, 2, 4, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1712732 : Nat := 118140960795 + 1712732 * 2 ^ 59
def prefixEnd_1712732 : Nat := 4983230072969 + 3 ^ 40 * 1712732 * 2
def baseEnd_1712732 : Nat := 879454748336498161873295

theorem tailTrace_1712732 : CollatzResearch.WordTrace tailWord_1712732 prefixEnd_1712732 879454748336498161873295 := by
  unfold tailWord_1712732
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234234015535975091346225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41645645354047966788461633 31234234015535975091346225)
  ·
    refine ⟨23425675511651981318509669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31234234015535975091346225 23425675511651981318509669)
    ·
      refine ⟨4392314158434746497220563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23425675511651981318509669 4392314158434746497220563)
      ·
        refine ⟨6588471237652119745830845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392314158434746497220563 6588471237652119745830845)
        ·
          refine ⟨2470676714119544904686567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6588471237652119745830845 2470676714119544904686567)
          ·
            refine ⟨3706015071179317357029851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470676714119544904686567 3706015071179317357029851)
            ·
              refine ⟨5559022606768976035544777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706015071179317357029851 5559022606768976035544777)
              ·
                refine ⟨4169266955076732026658583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5559022606768976035544777 4169266955076732026658583)
                ·
                  refine ⟨6253900432615098039987875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169266955076732026658583 6253900432615098039987875)
                  ·
                    refine ⟨9380850648922647059981813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6253900432615098039987875 9380850648922647059981813)
                    ·
                      refine ⟨879454748336498161873295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9380850648922647059981813 879454748336498161873295)
                      ·
                        rfl

theorem cell23_1712732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1712732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712732 prefixEnd_1712732 := by exact prefixLift 1712732
  have htrace : WordTrace (prefixWord ++ tailWord_1712732) baseStart_1712732 baseEnd_1712732 := by
    simpa [prefixWord, tailWord_1712732, baseEnd_1712732] using wordTrace_append hprefix tailTrace_1712732
  have hstable : (prefixWord ++ tailWord_1712732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712732).length < 2 ^ (prefixWord ++ tailWord_1712732).sum := by decide
  have hdescent : baseEnd_1712732 < baseStart_1712732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712748 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_1712748 : Nat := 118140960795 + 1712748 * 2 ^ 59
def prefixEnd_1712748 : Nat := 4983230072969 + 3 ^ 40 * 1712748 * 2
def baseEnd_1712748 : Nat := 293154321342323366424407

theorem tailTrace_1712748 : CollatzResearch.WordTrace tailWord_1712748 prefixEnd_1712748 293154321342323366424407 := by
  unfold tailWord_1712748
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234525799506992457637449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41646034399342656610183265 31234525799506992457637449)
  ·
    refine ⟨23425894349630244343228087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31234525799506992457637449 23425894349630244343228087)
    ·
      refine ⟨35138841524445366514842131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23425894349630244343228087 35138841524445366514842131)
      ·
        refine ⟨52708262286668049772263197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35138841524445366514842131 52708262286668049772263197)
        ·
          refine ⟨19765598357500518664598699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52708262286668049772263197 19765598357500518664598699)
          ·
            refine ⟨29648397536250777996898049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19765598357500518664598699 29648397536250777996898049)
            ·
              refine ⟨22236298152188083497673537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29648397536250777996898049 22236298152188083497673537)
              ·
                refine ⟨16677223614141062623255153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22236298152188083497673537 16677223614141062623255153)
                ·
                  refine ⟨12507917710605796967441365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16677223614141062623255153 12507917710605796967441365)
                  ·
                    refine ⟨293154321342323366424407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12507917710605796967441365 293154321342323366424407)
                    ·
                      rfl

theorem cell23_1712748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_1712748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712748 prefixEnd_1712748 := by exact prefixLift 1712748
  have htrace : WordTrace (prefixWord ++ tailWord_1712748) baseStart_1712748 baseEnd_1712748 := by
    simpa [prefixWord, tailWord_1712748, baseEnd_1712748] using wordTrace_append hprefix tailTrace_1712748
  have hstable : (prefixWord ++ tailWord_1712748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712748).length < 2 ^ (prefixWord ++ tailWord_1712748).sum := by decide
  have hdescent : baseEnd_1712748 < baseStart_1712748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712749 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_1712749 : Nat := 118140960795 + 1712749 * 2 ^ 59
def prefixEnd_1712749 : Nat := 4983230072969 + 3 ^ 40 * 1712749 * 2
def baseEnd_1712749 : Nat := 879463477507624595360717

theorem tailTrace_1712749 : CollatzResearch.WordTrace tailWord_1712749 prefixEnd_1712749 879463477507624595360717 := by
  unfold tailWord_1712749
  simp only [CollatzResearch.WordTrace]
  refine ⟨62469088072010362086061301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41646058714673574724040867 62469088072010362086061301)
  ·
    refine ⟨5856477006750971445568247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62469088072010362086061301 5856477006750971445568247)
    ·
      refine ⟨8784715510126457168352371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5856477006750971445568247 8784715510126457168352371)
      ·
        refine ⟨13177073265189685752528557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8784715510126457168352371 13177073265189685752528557)
        ·
          refine ⟨4941402474446132157198209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13177073265189685752528557 4941402474446132157198209)
          ·
            refine ⟨3706051855834599117898657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4941402474446132157198209 3706051855834599117898657)
            ·
              refine ⟨2779538891875949338423993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706051855834599117898657 2779538891875949338423993)
              ·
                refine ⟨2084654168906962003817995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779538891875949338423993 2084654168906962003817995)
                ·
                  refine ⟨3126981253360443005726993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084654168906962003817995 3126981253360443005726993)
                  ·
                    refine ⟨2345235940020332254295245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3126981253360443005726993 2345235940020332254295245)
                    ·
                      refine ⟨879463477507624595360717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2345235940020332254295245 879463477507624595360717)
                      ·
                        rfl

theorem cell23_1712749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_1712749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712749 prefixEnd_1712749 := by exact prefixLift 1712749
  have htrace : WordTrace (prefixWord ++ tailWord_1712749) baseStart_1712749 baseEnd_1712749 := by
    simpa [prefixWord, tailWord_1712749, baseEnd_1712749] using wordTrace_append hprefix tailTrace_1712749
  have hstable : (prefixWord ++ tailWord_1712749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712749).length < 2 ^ (prefixWord ++ tailWord_1712749).sum := by decide
  have hdescent : baseEnd_1712749 < baseStart_1712749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712752 : List Nat := [2, 1, 1, 1, 7, 2, 2, 7]
def baseStart_1712752 : Nat := 118140960795 + 1712752 * 2 ^ 59
def prefixEnd_1712752 : Nat := 4983230072969 + 3 ^ 40 * 1712752 * 2
def baseEnd_1712752 : Nat := 32572778442577336430489

theorem tailTrace_1712752 : CollatzResearch.WordTrace tailWord_1712752 prefixEnd_1712752 32572778442577336430489 := by
  unfold tailWord_1712752
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234598745499746799210255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41646131660666329065613673 31234598745499746799210255)
  ·
    refine ⟨46851898118249620198815383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31234598745499746799210255 46851898118249620198815383)
    ·
      refine ⟨70277847177374430298223075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46851898118249620198815383 70277847177374430298223075)
      ·
        refine ⟨105416770766061645447334613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70277847177374430298223075 105416770766061645447334613)
        ·
          refine ⟨2470705564829569815171905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 105416770766061645447334613 2470705564829569815171905)
          ·
            refine ⟨1853029173622177361378929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470705564829569815171905 1853029173622177361378929)
            ·
              refine ⟨1389771880216633021034197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853029173622177361378929 1389771880216633021034197)
              ·
                refine ⟨32572778442577336430489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1389771880216633021034197 32572778442577336430489)
                ·
                  rfl

theorem cell23_1712752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 7].length) (baseStart_1712752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712752 prefixEnd_1712752 := by exact prefixLift 1712752
  have htrace : WordTrace (prefixWord ++ tailWord_1712752) baseStart_1712752 baseEnd_1712752 := by
    simpa [prefixWord, tailWord_1712752, baseEnd_1712752] using wordTrace_append hprefix tailTrace_1712752
  have hstable : (prefixWord ++ tailWord_1712752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712752).length < 2 ^ (prefixWord ++ tailWord_1712752).sum := by decide
  have hdescent : baseEnd_1712752 < baseStart_1712752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712796 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1712796 : Nat := 118140960795 + 1712796 * 2 ^ 59
def prefixEnd_1712796 : Nat := 4983230072969 + 3 ^ 40 * 1712796 * 2
def baseEnd_1712796 : Nat := 879487611098385911473001

theorem tailTrace_1712796 : CollatzResearch.WordTrace tailWord_1712796 prefixEnd_1712796 879487611098385911473001 := by
  unfold tailWord_1712796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31235401151420044556511121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41647201535226726075348161 31235401151420044556511121)
  ·
    refine ⟨23426550863565033417383341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31235401151420044556511121 23426550863565033417383341)
    ·
      refine ⟨8784956573836887531518753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23426550863565033417383341 8784956573836887531518753)
      ·
        refine ⟨6588717430377665648639065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8784956573836887531518753 6588717430377665648639065)
        ·
          refine ⟨4941538072783249236479299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6588717430377665648639065 4941538072783249236479299)
          ·
            refine ⟨7412307109174873854718949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941538072783249236479299 7412307109174873854718949)
            ·
              refine ⟨1389807582970288847759803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7412307109174873854718949 1389807582970288847759803)
              ·
                refine ⟨2084711374455433271639705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389807582970288847759803 2084711374455433271639705)
                ·
                  refine ⟨1563533530841574953729779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084711374455433271639705 1563533530841574953729779)
                  ·
                    refine ⟨2345300296262362430594669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1563533530841574953729779 2345300296262362430594669)
                    ·
                      refine ⟨879487611098385911473001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2345300296262362430594669 879487611098385911473001)
                      ·
                        rfl

theorem cell23_1712796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1712796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712796 prefixEnd_1712796 := by exact prefixLift 1712796
  have htrace : WordTrace (prefixWord ++ tailWord_1712796) baseStart_1712796 baseEnd_1712796 := by
    simpa [prefixWord, tailWord_1712796, baseEnd_1712796] using wordTrace_append hprefix tailTrace_1712796
  have hstable : (prefixWord ++ tailWord_1712796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712796).length < 2 ^ (prefixWord ++ tailWord_1712796).sum := by decide
  have hdescent : baseEnd_1712796 < baseStart_1712796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712836 : List Nat := [2, 3, 3, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_1712836 : Nat := 118140960795 + 1712836 * 2 ^ 59
def prefixEnd_1712836 : Nat := 4983230072969 + 3 ^ 40 * 1712836 * 2
def baseEnd_1712836 : Nat := 879508150324565754972817

theorem tailTrace_1712836 : CollatzResearch.WordTrace tailWord_1712836 prefixEnd_1712836 879508150324565754972817 := by
  unfold tailWord_1712836
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236130611347587972239181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41648174148463450629652241 31236130611347587972239181)
  ·
    refine ⟨11713548979255345489589693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31236130611347587972239181 11713548979255345489589693)
    ·
      refine ⟨4392580867220754558596135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11713548979255345489589693 4392580867220754558596135)
      ·
        refine ⟨6588871300831131837894203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392580867220754558596135 6588871300831131837894203)
        ·
          refine ⟨9883306951246697756841305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588871300831131837894203 9883306951246697756841305)
          ·
            refine ⟨7412480213435023317630979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9883306951246697756841305 7412480213435023317630979)
            ·
              refine ⟨11118720320152534976446469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7412480213435023317630979 11118720320152534976446469)
              ·
                refine ⟨2084760060028600308083713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11118720320152534976446469 2084760060028600308083713)
                ·
                  refine ⟨1563570045021450231062785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084760060028600308083713 1563570045021450231062785)
                  ·
                    refine ⟨1172677533766087673297089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563570045021450231062785 1172677533766087673297089)
                    ·
                      refine ⟨879508150324565754972817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172677533766087673297089 879508150324565754972817)
                      ·
                        rfl

theorem cell23_1712836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_1712836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712836 prefixEnd_1712836 := by exact prefixLift 1712836
  have htrace : WordTrace (prefixWord ++ tailWord_1712836) baseStart_1712836 baseEnd_1712836 := by
    simpa [prefixWord, tailWord_1712836, baseEnd_1712836] using wordTrace_append hprefix tailTrace_1712836
  have hstable : (prefixWord ++ tailWord_1712836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712836).length < 2 ^ (prefixWord ++ tailWord_1712836).sum := by decide
  have hdescent : baseEnd_1712836 < baseStart_1712836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712872 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_1712872 : Nat := 118140960795 + 1712872 * 2 ^ 59
def prefixEnd_1712872 : Nat := 4983230072969 + 3 ^ 40 * 1712872 * 2
def baseEnd_1712872 : Nat := 293175545209375871374217

theorem tailTrace_1712872 : CollatzResearch.WordTrace tailWord_1712872 prefixEnd_1712872 293175545209375871374217 := by
  unfold tailWord_1712872
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236787125282377046394435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41649049500376502728525913 31236787125282377046394435)
  ·
    refine ⟨46855180687923565569591653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31236787125282377046394435 46855180687923565569591653)
    ·
      refine ⟨8785346378985668544298435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46855180687923565569591653 8785346378985668544298435)
      ·
        refine ⟨13178019568478502816447653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8785346378985668544298435 13178019568478502816447653)
        ·
          refine ⟨2470878669089719278083935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13178019568478502816447653 2470878669089719278083935)
          ·
            refine ⟨3706318003634578917125903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470878669089719278083935 3706318003634578917125903)
            ·
              refine ⟨5559477005451868375688855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706318003634578917125903 5559477005451868375688855)
              ·
                refine ⟨8339215508177802563533283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559477005451868375688855 8339215508177802563533283)
                ·
                  refine ⟨12508823262266703845299925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8339215508177802563533283 12508823262266703845299925)
                  ·
                    refine ⟨293175545209375871374217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12508823262266703845299925 293175545209375871374217)
                    ·
                      rfl

theorem cell23_1712872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_1712872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712872 prefixEnd_1712872 := by exact prefixLift 1712872
  have htrace : WordTrace (prefixWord ++ tailWord_1712872) baseStart_1712872 baseEnd_1712872 := by
    simpa [prefixWord, tailWord_1712872, baseEnd_1712872] using wordTrace_append hprefix tailTrace_1712872
  have hstable : (prefixWord ++ tailWord_1712872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712872).length < 2 ^ (prefixWord ++ tailWord_1712872).sum := by decide
  have hdescent : baseEnd_1712872 < baseStart_1712872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712975 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 7, 6]
def baseStart_1712975 : Nat := 118140960795 + 1712975 * 2 ^ 59
def prefixEnd_1712975 : Nat := 4983230072969 + 3 ^ 40 * 1712975 * 2
def baseEnd_1712975 : Nat := 293193174711846903711559

theorem tailTrace_1712975 : CollatzResearch.WordTrace tailWord_1712975 prefixEnd_1712975 293193174711846903711559 := by
  unfold tailWord_1712975
  simp only [CollatzResearch.WordTrace]
  refine ⟨62477330969191602683788379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41651553979461068455858919 62477330969191602683788379)
  ·
    refine ⟨93715996453787404025682569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62477330969191602683788379 93715996453787404025682569)
    ·
      refine ⟨70286997340340553019261927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93715996453787404025682569 70286997340340553019261927)
      ·
        refine ⟨105430496010510829528892891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70286997340340553019261927 105430496010510829528892891)
        ·
          refine ⟨158145744015766244293339337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105430496010510829528892891 158145744015766244293339337)
          ·
            refine ⟨118609308011824683220004503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158145744015766244293339337 118609308011824683220004503)
            ·
              refine ⟨177913962017737024830006755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118609308011824683220004503 177913962017737024830006755)
              ·
                refine ⟨266870943026605537245010133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177913962017737024830006755 266870943026605537245010133)
                ·
                  refine ⟨6254787727186067279179925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266870943026605537245010133 6254787727186067279179925)
                  ·
                    refine ⟨293193174711846903711559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6254787727186067279179925 293193174711846903711559)
                    ·
                      rfl

theorem cell23_1712975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 6].length) (baseStart_1712975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712975 prefixEnd_1712975 := by exact prefixLift 1712975
  have htrace : WordTrace (prefixWord ++ tailWord_1712975) baseStart_1712975 baseEnd_1712975 := by
    simpa [prefixWord, tailWord_1712975, baseEnd_1712975] using wordTrace_append hprefix tailTrace_1712975
  have hstable : (prefixWord ++ tailWord_1712975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712975).length < 2 ^ (prefixWord ++ tailWord_1712975).sum := by decide
  have hdescent : baseEnd_1712975 < baseStart_1712975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712986 : List Nat := [3, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2]
def baseStart_1712986 : Nat := 118140960795 + 1712986 * 2 ^ 59
def prefixEnd_1712986 : Nat := 4983230072969 + 3 ^ 40 * 1712986 * 2
def baseEnd_1712986 : Nat := 879585172422740168097127

theorem tailTrace_1712986 : CollatzResearch.WordTrace tailWord_1712986 prefixEnd_1712986 879585172422740168097127 := by
  unfold tailWord_1712986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15619433043037937890609703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41651821448101167708292541 15619433043037937890609703)
  ·
    refine ⟨23429149564556906835914555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15619433043037937890609703 23429149564556906835914555)
    ·
      refine ⟨35143724346835360253871833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429149564556906835914555 35143724346835360253871833)
      ·
        refine ⟨26357793260126520190403875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35143724346835360253871833 26357793260126520190403875)
        ·
          refine ⟨39536689890189780285605813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26357793260126520190403875 39536689890189780285605813)
          ·
            refine ⟨3706564677205291901775545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39536689890189780285605813 3706564677205291901775545)
            ·
              refine ⟨2779923507903968926331659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706564677205291901775545 2779923507903968926331659)
              ·
                refine ⟨4169885261855953389497489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779923507903968926331659 4169885261855953389497489)
                ·
                  refine ⟨3127413946391965042123117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169885261855953389497489 3127413946391965042123117)
                  ·
                    refine ⟨1172780229896986890796169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127413946391965042123117 1172780229896986890796169)
                    ·
                      refine ⟨879585172422740168097127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172780229896986890796169 879585172422740168097127)
                      ·
                        rfl

theorem cell23_1712986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_1712986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712986 prefixEnd_1712986 := by exact prefixLift 1712986
  have htrace : WordTrace (prefixWord ++ tailWord_1712986) baseStart_1712986 baseEnd_1712986 := by
    simpa [prefixWord, tailWord_1712986, baseEnd_1712986] using wordTrace_append hprefix tailTrace_1712986
  have hstable : (prefixWord ++ tailWord_1712986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712986).length < 2 ^ (prefixWord ++ tailWord_1712986).sum := by decide
  have hdescent : baseEnd_1712986 < baseStart_1712986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712992 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_1712992 : Nat := 118140960795 + 1712992 * 2 ^ 59
def prefixEnd_1712992 : Nat := 4983230072969 + 3 ^ 40 * 1712992 * 2
def baseEnd_1712992 : Nat := 293196084435555714874033

theorem tailTrace_1712992 : CollatzResearch.WordTrace tailWord_1712992 prefixEnd_1712992 293196084435555714874033 := by
  unfold tailWord_1712992
  simp only [CollatzResearch.WordTrace]
  refine ⟨31238975505065007293578615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41651967340086676391438153 31238975505065007293578615)
  ·
    refine ⟨46858463257597510940367923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31238975505065007293578615 46858463257597510940367923)
    ·
      refine ⟨70287694886396266410551885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46858463257597510940367923 70287694886396266410551885)
      ·
        refine ⟨26357885582398599903956957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70287694886396266410551885 26357885582398599903956957)
        ·
          refine ⟨9884207093399474963983859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26357885582398599903956957 9884207093399474963983859)
          ·
            refine ⟨14826310640099212445975789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884207093399474963983859 14826310640099212445975789)
            ·
              refine ⟨5559866490037204667240921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14826310640099212445975789 5559866490037204667240921)
              ·
                refine ⟨4169899867527903500430691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5559866490037204667240921 4169899867527903500430691)
                ·
                  refine ⟨6254849801291855250646037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169899867527903500430691 6254849801291855250646037)
                  ·
                    refine ⟨293196084435555714874033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6254849801291855250646037 293196084435555714874033)
                    ·
                      rfl

theorem cell23_1712992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_1712992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712992 prefixEnd_1712992 := by exact prefixLift 1712992
  have htrace : WordTrace (prefixWord ++ tailWord_1712992) baseStart_1712992 baseEnd_1712992 := by
    simpa [prefixWord, tailWord_1712992, baseEnd_1712992] using wordTrace_append hprefix tailTrace_1712992
  have hstable : (prefixWord ++ tailWord_1712992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712992).length < 2 ^ (prefixWord ++ tailWord_1712992).sum := by decide
  have hdescent : baseEnd_1712992 < baseStart_1712992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712996 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_1712996 : Nat := 118140960795 + 1712996 * 2 ^ 59
def prefixEnd_1712996 : Nat := 4983230072969 + 3 ^ 40 * 1712996 * 2
def baseEnd_1712996 : Nat := 293196769076428376324027

theorem tailTrace_1712996 : CollatzResearch.WordTrace tailWord_1712996 prefixEnd_1712996 293196769076428376324027 := by
  unfold tailWord_1712996
  simp only [CollatzResearch.WordTrace]
  refine ⟨31239048451057761635151421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41652064601410348846868561 31239048451057761635151421)
  ·
    refine ⟨11714643169146660613181783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31239048451057761635151421 11714643169146660613181783)
    ·
      refine ⟨17571964753719990919772675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11714643169146660613181783 17571964753719990919772675)
      ·
        refine ⟨26357947130579986379659013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17571964753719990919772675 26357947130579986379659013)
        ·
          refine ⟨4942115086983747446186065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26357947130579986379659013 4942115086983747446186065)
          ·
            refine ⟨3706586315237810584639549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4942115086983747446186065 3706586315237810584639549)
            ·
              refine ⟨1389969868214178969239831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3706586315237810584639549 1389969868214178969239831)
              ·
                refine ⟨2084954802321268453859747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389969868214178969239831 2084954802321268453859747)
                ·
                  refine ⟨3127432203481902680789621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084954802321268453859747 3127432203481902680789621)
                  ·
                    refine ⟨293196769076428376324027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3127432203481902680789621 293196769076428376324027)
                    ·
                      rfl

theorem cell23_1712996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_1712996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1712996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1712996 prefixEnd_1712996 := by exact prefixLift 1712996
  have htrace : WordTrace (prefixWord ++ tailWord_1712996) baseStart_1712996 baseEnd_1712996 := by
    simpa [prefixWord, tailWord_1712996, baseEnd_1712996] using wordTrace_append hprefix tailTrace_1712996
  have hstable : (prefixWord ++ tailWord_1712996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712996).length < 2 ^ (prefixWord ++ tailWord_1712996).sum := by decide
  have hdescent : baseEnd_1712996 < baseStart_1712996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713009 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 2, 4]
def baseStart_1713009 : Nat := 118140960795 + 1713009 * 2 ^ 59
def prefixEnd_1713009 : Nat := 4983230072969 + 3 ^ 40 * 1713009 * 2
def baseEnd_1713009 : Nat := 293198994159264526036507

theorem tailTrace_1713009 : CollatzResearch.WordTrace tailWord_1713009 prefixEnd_1713009 293198994159264526036507 := by
  unfold tailWord_1713009
  simp only [CollatzResearch.WordTrace]
  refine ⟨62478571051068426490526081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41652380700712284327017387 62478571051068426490526081)
  ·
    refine ⟨46858928288301319867894561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62478571051068426490526081 46858928288301319867894561)
    ·
      refine ⟨35144196216225989900920921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46858928288301319867894561 35144196216225989900920921)
      ·
        refine ⟨26358147162169492425690691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35144196216225989900920921 26358147162169492425690691)
        ·
          refine ⟨39537220743254238638536037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26358147162169492425690691 39537220743254238638536037)
          ·
            refine ⟨7413228889360169744725507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39537220743254238638536037 7413228889360169744725507)
            ·
              refine ⟨11119843334040254617088261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413228889360169744725507 11119843334040254617088261)
              ·
                refine ⟨2084970625132547740704049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11119843334040254617088261 2084970625132547740704049)
                ·
                  refine ⟨1563727968849410805528037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084970625132547740704049 1563727968849410805528037)
                  ·
                    refine ⟨293198994159264526036507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563727968849410805528037 293198994159264526036507)
                    ·
                      rfl

theorem cell23_1713009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_1713009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713009 prefixEnd_1713009 := by exact prefixLift 1713009
  have htrace : WordTrace (prefixWord ++ tailWord_1713009) baseStart_1713009 baseEnd_1713009 := by
    simpa [prefixWord, tailWord_1713009, baseEnd_1713009] using wordTrace_append hprefix tailTrace_1713009
  have hstable : (prefixWord ++ tailWord_1713009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713009).length < 2 ^ (prefixWord ++ tailWord_1713009).sum := by decide
  have hdescent : baseEnd_1713009 < baseStart_1713009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713029 : List Nat := [1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_1713029 : Nat := 118140960795 + 1713029 * 2 ^ 59
def prefixEnd_1713029 : Nat := 4983230072969 + 3 ^ 40 * 1713029 * 2
def baseEnd_1713029 : Nat := 879607252090883499859429

theorem tailTrace_1713029 : CollatzResearch.WordTrace tailWord_1713029 prefixEnd_1713029 879607252090883499859429 := by
  unfold tailWord_1713029
  simp only [CollatzResearch.WordTrace]
  refine ⟨62479300510995969906254141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41652867007330646604169427 62479300510995969906254141)
  ·
    refine ⟨23429737691623488714845303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62479300510995969906254141 23429737691623488714845303)
    ·
      refine ⟨35144606537435233072267955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429737691623488714845303 35144606537435233072267955)
      ·
        refine ⟨52716909806152849608401933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35144606537435233072267955 52716909806152849608401933)
        ·
          refine ⟨19768841177307318603150725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52716909806152849608401933 19768841177307318603150725)
          ·
            refine ⟨3706657720745122238090761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19768841177307318603150725 3706657720745122238090761)
            ·
              refine ⟨2779993290558841678568071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706657720745122238090761 2779993290558841678568071)
              ·
                refine ⟨4169989935838262517852107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779993290558841678568071 4169989935838262517852107)
                ·
                  refine ⟨6254984903757393776778161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169989935838262517852107 6254984903757393776778161)
                  ·
                    refine ⟨4691238677818045332583621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6254984903757393776778161 4691238677818045332583621)
                    ·
                      refine ⟨879607252090883499859429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4691238677818045332583621 879607252090883499859429)
                      ·
                        rfl

theorem cell23_1713029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_1713029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713029 prefixEnd_1713029 := by exact prefixLift 1713029
  have htrace : WordTrace (prefixWord ++ tailWord_1713029) baseStart_1713029 baseEnd_1713029 := by
    simpa [prefixWord, tailWord_1713029, baseEnd_1713029] using wordTrace_append hprefix tailTrace_1713029
  have hstable : (prefixWord ++ tailWord_1713029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713029).length < 2 ^ (prefixWord ++ tailWord_1713029).sum := by decide
  have hdescent : baseEnd_1713029 < baseStart_1713029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713049 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 3]
def baseStart_1713049 : Nat := 118140960795 + 1713049 * 2 ^ 59
def prefixEnd_1713049 : Nat := 4983230072969 + 3 ^ 40 * 1713049 * 2
def baseEnd_1713049 : Nat := 879617521703973421609337

theorem tailTrace_1713049 : CollatzResearch.WordTrace tailWord_1713049 prefixEnd_1713049 879617521703973421609337 := by
  unfold tailWord_1713049
  simp only [CollatzResearch.WordTrace]
  refine ⟨62480029970923513321982201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41653353313949008881321467 62480029970923513321982201)
  ·
    refine ⟨46860022478192634991486651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62480029970923513321982201 46860022478192634991486651)
    ·
      refine ⟨70290033717288952487229977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46860022478192634991486651 70290033717288952487229977)
      ·
        refine ⟨52717525287966714365422483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70290033717288952487229977 52717525287966714365422483)
        ·
          refine ⟨79076287931950071548133725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52717525287966714365422483 79076287931950071548133725)
          ·
            refine ⟨29653607974481276830550147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79076287931950071548133725 29653607974481276830550147)
            ·
              refine ⟨44480411961721915245825221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29653607974481276830550147 44480411961721915245825221)
              ·
                refine ⟨8340077242822859108592229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44480411961721915245825221 8340077242822859108592229)
                ·
                  refine ⟨1563764483029286082861043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8340077242822859108592229 1563764483029286082861043)
                  ·
                    refine ⟨2345646724543929124291565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1563764483029286082861043 2345646724543929124291565)
                    ·
                      refine ⟨879617521703973421609337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2345646724543929124291565 879617521703973421609337)
                      ·
                        rfl

theorem cell23_1713049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_1713049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713049 prefixEnd_1713049 := by exact prefixLift 1713049
  have htrace : WordTrace (prefixWord ++ tailWord_1713049) baseStart_1713049 baseEnd_1713049 := by
    simpa [prefixWord, tailWord_1713049, baseEnd_1713049] using wordTrace_append hprefix tailTrace_1713049
  have hstable : (prefixWord ++ tailWord_1713049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713049).length < 2 ^ (prefixWord ++ tailWord_1713049).sum := by decide
  have hdescent : baseEnd_1713049 < baseStart_1713049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713050 : List Nat := [3, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4]
def baseStart_1713050 : Nat := 118140960795 + 1713050 * 2 ^ 59
def prefixEnd_1713050 : Nat := 4983230072969 + 3 ^ 40 * 1713050 * 2
def baseEnd_1713050 : Nat := 879618035184627917696833

theorem tailTrace_1713050 : CollatzResearch.WordTrace tailWord_1713050 prefixEnd_1713050 879618035184627917696833 := by
  unfold tailWord_1713050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620016610979972623192151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41653377629279926995179069 15620016610979972623192151)
  ·
    refine ⟨23430024916469958934788227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620016610979972623192151 23430024916469958934788227)
    ·
      refine ⟨35145037374704938402182341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430024916469958934788227 35145037374704938402182341)
      ·
        refine ⟨6589694507757175950409189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35145037374704938402182341 6589694507757175950409189)
        ·
          refine ⟨1235567720204470490701723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6589694507757175950409189 1235567720204470490701723)
          ·
            refine ⟨1853351580306705736052585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235567720204470490701723 1853351580306705736052585)
            ·
              refine ⟨1390013685230029302039439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853351580306705736052585 1390013685230029302039439)
              ·
                refine ⟨2085020527845043953059159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390013685230029302039439 2085020527845043953059159)
                ·
                  refine ⟨3127530791767565929588739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085020527845043953059159 3127530791767565929588739)
                  ·
                    refine ⟨4691296187651348894383109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3127530791767565929588739 4691296187651348894383109)
                    ·
                      refine ⟨879618035184627917696833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4691296187651348894383109 879618035184627917696833)
                      ·
                        rfl

theorem cell23_1713050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_1713050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713050 prefixEnd_1713050 := by exact prefixLift 1713050
  have htrace : WordTrace (prefixWord ++ tailWord_1713050) baseStart_1713050 baseEnd_1713050 := by
    simpa [prefixWord, tailWord_1713050, baseEnd_1713050] using wordTrace_append hprefix tailTrace_1713050
  have hstable : (prefixWord ++ tailWord_1713050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713050).length < 2 ^ (prefixWord ++ tailWord_1713050).sum := by decide
  have hdescent : baseEnd_1713050 < baseStart_1713050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713082 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 2, 6]
def baseStart_1713082 : Nat := 118140960795 + 1713082 * 2 ^ 59
def prefixEnd_1713082 : Nat := 4983230072969 + 3 ^ 40 * 1713082 * 2
def baseEnd_1713082 : Nat := 293211488855190597498895

theorem tailTrace_1713082 : CollatzResearch.WordTrace tailWord_1713082 prefixEnd_1713082 293211488855190597498895 := by
  unfold tailWord_1713082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15620308394950989989483375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41654155719869306638622333 15620308394950989989483375)
  ·
    refine ⟨23430462592426484984225063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15620308394950989989483375 23430462592426484984225063)
    ·
      refine ⟨35145693888639727476337595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430462592426484984225063 35145693888639727476337595)
      ·
        refine ⟨52718540832959591214506393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35145693888639727476337595 52718540832959591214506393)
        ·
          refine ⟨39538905624719693410879795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52718540832959591214506393 39538905624719693410879795)
          ·
            refine ⟨59308358437079540116319693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39538905624719693410879795 59308358437079540116319693)
            ·
              refine ⟨22240634413904827543619885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59308358437079540116319693 22240634413904827543619885)
              ·
                refine ⟨8340237905214310328857457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22240634413904827543619885 8340237905214310328857457)
                ·
                  refine ⟨6255178428910732746643093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8340237905214310328857457 6255178428910732746643093)
                  ·
                    refine ⟨293211488855190597498895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6255178428910732746643093 293211488855190597498895)
                    ·
                      rfl

theorem cell23_1713082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 6].length) (baseStart_1713082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713082 prefixEnd_1713082 := by exact prefixLift 1713082
  have htrace : WordTrace (prefixWord ++ tailWord_1713082) baseStart_1713082 baseEnd_1713082 := by
    simpa [prefixWord, tailWord_1713082, baseEnd_1713082] using wordTrace_append hprefix tailTrace_1713082
  have hstable : (prefixWord ++ tailWord_1713082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713082).length < 2 ^ (prefixWord ++ tailWord_1713082).sum := by decide
  have hdescent : baseEnd_1713082 < baseStart_1713082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713110 : List Nat := [5, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2]
def baseStart_1713110 : Nat := 118140960795 + 1713110 * 2 ^ 59
def prefixEnd_1713110 : Nat := 4983230072969 + 3 ^ 40 * 1713110 * 2
def baseEnd_1713110 : Nat := 879648844023897682946557

theorem tailTrace_1713110 : CollatzResearch.WordTrace tailWord_1713110 prefixEnd_1713110 879648844023897682946557 := by
  unfold tailWord_1713110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905140926481407546247049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41654836549135013826635189 3905140926481407546247049)
  ·
    refine ⟨2928855694861055659685287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3905140926481407546247049 2928855694861055659685287)
    ·
      refine ⟨4393283542291583489527931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2928855694861055659685287 4393283542291583489527931)
      ·
        refine ⟨6589925313437375234291897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4393283542291583489527931 6589925313437375234291897)
        ·
          refine ⟨4942443985078031425718923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6589925313437375234291897 4942443985078031425718923)
          ·
            refine ⟨7413665977617047138578385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942443985078031425718923 7413665977617047138578385)
            ·
              refine ⟨5560249483212785353933789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7413665977617047138578385 5560249483212785353933789)
              ·
                refine ⟨2085093556204794507725171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5560249483212785353933789 2085093556204794507725171)
                ·
                  refine ⟨3127640334307191761587757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085093556204794507725171 3127640334307191761587757)
                  ·
                    refine ⟨1172865125365196910595409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3127640334307191761587757 1172865125365196910595409)
                    ·
                      refine ⟨879648844023897682946557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172865125365196910595409 879648844023897682946557)
                      ·
                        rfl

theorem cell23_1713110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_1713110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713110 prefixEnd_1713110 := by exact prefixLift 1713110
  have htrace : WordTrace (prefixWord ++ tailWord_1713110) baseStart_1713110 baseEnd_1713110 := by
    simpa [prefixWord, tailWord_1713110, baseEnd_1713110] using wordTrace_append hprefix tailTrace_1713110
  have hstable : (prefixWord ++ tailWord_1713110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713110).length < 2 ^ (prefixWord ++ tailWord_1713110).sum := by decide
  have hdescent : baseEnd_1713110 < baseStart_1713110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713123 : List Nat := [1, 1, 1, 6, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1713123 : Nat := 118140960795 + 1713123 * 2 ^ 59
def prefixEnd_1713123 : Nat := 4983230072969 + 3 ^ 40 * 1713123 * 2
def baseEnd_1713123 : Nat := 879655519272406132083997

theorem tailTrace_1713123 : CollatzResearch.WordTrace tailWord_1713123 prefixEnd_1713123 879655519272406132083997 := by
  unfold tailWord_1713123
  simp only [CollatzResearch.WordTrace]
  refine ⟨62482728972655423960176023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41655152648436949306784015 62482728972655423960176023)
  ·
    refine ⟨93724093458983135940264035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62482728972655423960176023 93724093458983135940264035)
    ·
      refine ⟨140586140188474703910396053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93724093458983135940264035 140586140188474703910396053)
      ·
        refine ⟨6589975321334751745799815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 140586140188474703910396053 6589975321334751745799815)
        ·
          refine ⟨9884962982002127618699723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6589975321334751745799815 9884962982002127618699723)
          ·
            refine ⟨14827444473003191428049585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9884962982002127618699723 14827444473003191428049585)
            ·
              refine ⟨11120583354752393571037189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14827444473003191428049585 11120583354752393571037189)
              ·
                refine ⟨2085109379016073794569473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11120583354752393571037189 2085109379016073794569473)
                ·
                  refine ⟨1563832034262055345927105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085109379016073794569473 1563832034262055345927105)
                  ·
                    refine ⟨1172874025696541509445329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1563832034262055345927105 1172874025696541509445329)
                    ·
                      refine ⟨879655519272406132083997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172874025696541509445329 879655519272406132083997)
                      ·
                        rfl

theorem cell23_1713123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1713123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713123 prefixEnd_1713123 := by exact prefixLift 1713123
  have htrace : WordTrace (prefixWord ++ tailWord_1713123) baseStart_1713123 baseEnd_1713123 := by
    simpa [prefixWord, tailWord_1713123, baseEnd_1713123] using wordTrace_append hprefix tailTrace_1713123
  have hstable : (prefixWord ++ tailWord_1713123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713123).length < 2 ^ (prefixWord ++ tailWord_1713123).sum := by decide
  have hdescent : baseEnd_1713123 < baseStart_1713123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713180 : List Nat := [2, 2, 3, 1, 4, 2, 2, 2, 5]
def baseStart_1713180 : Nat := 118140960795 + 1713180 * 2 ^ 59
def prefixEnd_1713180 : Nat := 4983230072969 + 3 ^ 40 * 1713180 * 2
def baseEnd_1713180 : Nat := 97742754185523601007915

theorem tailTrace_1713180 : CollatzResearch.WordTrace tailWord_1713180 prefixEnd_1713180 97742754185523601007915 := by
  unfold tailWord_1713180
  simp only [CollatzResearch.WordTrace]
  refine ⟨31242403966724461347500497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41656538622299281796667329 31242403966724461347500497)
  ·
    refine ⟨23431802975043346010625373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31242403966724461347500497 23431802975043346010625373)
    ·
      refine ⟨8786926115641254753984515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23431802975043346010625373 8786926115641254753984515)
      ·
        refine ⟨13180389173461882130976773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8786926115641254753984515 13180389173461882130976773)
        ·
          refine ⟨2471322970024102899558145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13180389173461882130976773 2471322970024102899558145)
          ·
            refine ⟨1853492227518077174668609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2471322970024102899558145 1853492227518077174668609)
            ·
              refine ⟨1390119170638557881001457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853492227518077174668609 1390119170638557881001457)
              ·
                refine ⟨1042589377978918410751093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390119170638557881001457 1042589377978918410751093)
                ·
                  refine ⟨97742754185523601007915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1042589377978918410751093 97742754185523601007915)
                  ·
                    rfl

theorem cell23_1713180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_1713180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713180 prefixEnd_1713180 := by exact prefixLift 1713180
  have htrace : WordTrace (prefixWord ++ tailWord_1713180) baseStart_1713180 baseEnd_1713180 := by
    simpa [prefixWord, tailWord_1713180, baseEnd_1713180] using wordTrace_append hprefix tailTrace_1713180
  have hstable : (prefixWord ++ tailWord_1713180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713180).length < 2 ^ (prefixWord ++ tailWord_1713180).sum := by decide
  have hdescent : baseEnd_1713180 < baseStart_1713180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713196 : List Nat := [2, 2, 1, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_1713196 : Nat := 118140960795 + 1713196 * 2 ^ 59
def prefixEnd_1713196 : Nat := 4983230072969 + 3 ^ 40 * 1713196 * 2
def baseEnd_1713196 : Nat := 879693003360184346471161

theorem tailTrace_1713196 : CollatzResearch.WordTrace tailWord_1713196 prefixEnd_1713196 879693003360184346471161 := by
  unfold tailWord_1713196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31242695750695478713791721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41656927667593971618388961 31242695750695478713791721)
  ·
    refine ⟨23432021813021609035343791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31242695750695478713791721 23432021813021609035343791)
    ·
      refine ⟨35148032719532413553015687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23432021813021609035343791 35148032719532413553015687)
      ·
        refine ⟨52722049079298620329523531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35148032719532413553015687 52722049079298620329523531)
        ·
          refine ⟨79083073618947930494285297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52722049079298620329523531 79083073618947930494285297)
          ·
            refine ⟨59312305214210947870713973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79083073618947930494285297 59312305214210947870713973)
            ·
              refine ⟨5560528613832276362879435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59312305214210947870713973 5560528613832276362879435)
              ·
                refine ⟨8340792920748414544319153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560528613832276362879435 8340792920748414544319153)
                ·
                  refine ⟨6255594690561310908239365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8340792920748414544319153 6255594690561310908239365)
                  ·
                    refine ⟨1172924004480245795294881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6255594690561310908239365 1172924004480245795294881)
                    ·
                      refine ⟨879693003360184346471161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1172924004480245795294881 879693003360184346471161)
                      ·
                        rfl

theorem cell23_1713196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_1713196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713196 prefixEnd_1713196 := by exact prefixLift 1713196
  have htrace : WordTrace (prefixWord ++ tailWord_1713196) baseStart_1713196 baseEnd_1713196 := by
    simpa [prefixWord, tailWord_1713196, baseEnd_1713196] using wordTrace_append hprefix tailTrace_1713196
  have hstable : (prefixWord ++ tailWord_1713196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713196).length < 2 ^ (prefixWord ++ tailWord_1713196).sum := by decide
  have hdescent : baseEnd_1713196 < baseStart_1713196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713213 : List Nat := [1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1713213 : Nat := 118140960795 + 1713213 * 2 ^ 59
def prefixEnd_1713213 : Nat := 4983230072969 + 3 ^ 40 * 1713213 * 2
def baseEnd_1713213 : Nat := 879701732531310779958583

theorem tailTrace_1713213 : CollatzResearch.WordTrace tailWord_1713213 prefixEnd_1713213 879701732531310779958583 := by
  unfold tailWord_1713213
  simp only [CollatzResearch.WordTrace]
  refine ⟨62486011542329369330952293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41657341028219579553968195 62486011542329369330952293)
  ·
    refine ⟨11716127164186756749553555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62486011542329369330952293 11716127164186756749553555)
    ·
      refine ⟨17574190746280135124330333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11716127164186756749553555 17574190746280135124330333)
      ·
        refine ⟨6590321529855050671623875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17574190746280135124330333 6590321529855050671623875)
        ·
          refine ⟨9885482294782576007435813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590321529855050671623875 9885482294782576007435813)
          ·
            refine ⟨1853527930271733001394215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9885482294782576007435813 1853527930271733001394215)
            ·
              refine ⟨2780291895407599502091323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853527930271733001394215 2780291895407599502091323)
              ·
                refine ⟨4170437843111399253136985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780291895407599502091323 4170437843111399253136985)
                ·
                  refine ⟨3127828382333549439852739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170437843111399253136985 3127828382333549439852739)
                  ·
                    refine ⟨4691742573500324159779109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3127828382333549439852739 4691742573500324159779109)
                    ·
                      refine ⟨879701732531310779958583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4691742573500324159779109 879701732531310779958583)
                      ·
                        rfl

theorem cell23_1713213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1713213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713213 prefixEnd_1713213 := by exact prefixLift 1713213
  have htrace : WordTrace (prefixWord ++ tailWord_1713213) baseStart_1713213 baseEnd_1713213 := by
    simpa [prefixWord, tailWord_1713213, baseEnd_1713213] using wordTrace_append hprefix tailTrace_1713213
  have hstable : (prefixWord ++ tailWord_1713213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713213).length < 2 ^ (prefixWord ++ tailWord_1713213).sum := by decide
  have hdescent : baseEnd_1713213 < baseStart_1713213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713223 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 1, 4]
def baseStart_1713223 : Nat := 118140960795 + 1713223 * 2 ^ 59
def prefixEnd_1713223 : Nat := 4983230072969 + 3 ^ 40 * 1713223 * 2
def baseEnd_1713223 : Nat := 293235622445951913611179

theorem tailTrace_1713223 : CollatzResearch.WordTrace tailWord_1713223 prefixEnd_1713223 293235622445951913611179 := by
  unfold tailWord_1713223
  simp only [CollatzResearch.WordTrace]
  refine ⟨62486376272293141038816323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41657584181528760692544215 62486376272293141038816323)
  ·
    refine ⟨93729564408439711558224485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62486376272293141038816323 93729564408439711558224485)
    ·
      refine ⟨17574293326582445917167091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93729564408439711558224485 17574293326582445917167091)
      ·
        refine ⟨26361439989873668875750637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17574293326582445917167091 26361439989873668875750637)
        ·
          refine ⟨9885539996202625828406489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26361439989873668875750637 9885539996202625828406489)
          ·
            refine ⟨7414154997151969371304867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9885539996202625828406489 7414154997151969371304867)
            ·
              refine ⟨11121232495727954056957301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7414154997151969371304867 11121232495727954056957301)
              ·
                refine ⟨1042615546474495692839747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11121232495727954056957301 1042615546474495692839747)
                ·
                  refine ⟨1563923319711743539259621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042615546474495692839747 1563923319711743539259621)
                  ·
                    refine ⟨293235622445951913611179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1563923319711743539259621 293235622445951913611179)
                    ·
                      rfl

theorem cell23_1713223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_1713223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713223 prefixEnd_1713223 := by exact prefixLift 1713223
  have htrace : WordTrace (prefixWord ++ tailWord_1713223) baseStart_1713223 baseEnd_1713223 := by
    simpa [prefixWord, tailWord_1713223, baseEnd_1713223] using wordTrace_append hprefix tailTrace_1713223
  have hstable : (prefixWord ++ tailWord_1713223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713223).length < 2 ^ (prefixWord ++ tailWord_1713223).sum := by decide
  have hdescent : baseEnd_1713223 < baseStart_1713223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713236 : List Nat := [2, 4, 1, 1, 1, 1, 5, 2, 6]
def baseStart_1713236 : Nat := 118140960795 + 1713236 * 2 ^ 59
def prefixEnd_1713236 : Nat := 4983230072969 + 3 ^ 40 * 1713236 * 2
def baseEnd_1713236 : Nat := 97745949176262687774553

theorem tailTrace_1713236 : CollatzResearch.WordTrace tailWord_1713236 prefixEnd_1713236 97745949176262687774553 := by
  unfold tailWord_1713236
  simp only [CollatzResearch.WordTrace]
  refine ⟨31243425210623022129519781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41657900280830696172693041 31243425210623022129519781)
  ·
    refine ⟨5858142226991816649284959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31243425210623022129519781 5858142226991816649284959)
    ·
      refine ⟨8787213340487724973927439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858142226991816649284959 8787213340487724973927439)
      ·
        refine ⟨13180820010731587460891159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8787213340487724973927439 13180820010731587460891159)
        ·
          refine ⟨19771230016097381191336739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13180820010731587460891159 19771230016097381191336739)
          ·
            refine ⟨29656845024146071787005109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19771230016097381191336739 29656845024146071787005109)
            ·
              refine ⟨2780329221013694230031729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29656845024146071787005109 2780329221013694230031729)
              ·
                refine ⟨2085246915760270672523797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780329221013694230031729 2085246915760270672523797)
                ·
                  refine ⟨97745949176262687774553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2085246915760270672523797 97745949176262687774553)
                  ·
                    rfl

theorem cell23_1713236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_1713236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713236 prefixEnd_1713236 := by exact prefixLift 1713236
  have htrace : WordTrace (prefixWord ++ tailWord_1713236) baseStart_1713236 baseEnd_1713236 := by
    simpa [prefixWord, tailWord_1713236, baseEnd_1713236] using wordTrace_append hprefix tailTrace_1713236
  have hstable : (prefixWord ++ tailWord_1713236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713236).length < 2 ^ (prefixWord ++ tailWord_1713236).sum := by decide
  have hdescent : baseEnd_1713236 < baseStart_1713236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713249 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 5, 5]
def baseStart_1713249 : Nat := 118140960795 + 1713249 * 2 ^ 59
def prefixEnd_1713249 : Nat := 4983230072969 + 3 ^ 40 * 1713249 * 2
def baseEnd_1713249 : Nat := 293240072611624213036139

theorem tailTrace_1713249 : CollatzResearch.WordTrace tailWord_1713249 prefixEnd_1713249 293240072611624213036139 := by
  unfold tailWord_1713249
  simp only [CollatzResearch.WordTrace]
  refine ⟨62487324570198947479262801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41658216380132631652841867 62487324570198947479262801)
  ·
    refine ⟨46865493427649210609447101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62487324570198947479262801 46865493427649210609447101)
    ·
      refine ⟨17574560035368453978542663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46865493427649210609447101 17574560035368453978542663)
      ·
        refine ⟨26361840053052680967813995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17574560035368453978542663 26361840053052680967813995)
        ·
          refine ⟨39542760079579021451720993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26361840053052680967813995 39542760079579021451720993)
          ·
            refine ⟨29657070059684266088790745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39542760079579021451720993 29657070059684266088790745)
            ·
              refine ⟨22242802544763199566593059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29657070059684266088790745 22242802544763199566593059)
              ·
                refine ⟨33364203817144799349889589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22242802544763199566593059 33364203817144799349889589)
                ·
                  refine ⟨3127894107857324939052149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33364203817144799349889589 3127894107857324939052149)
                  ·
                    refine ⟨293240072611624213036139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3127894107857324939052149 293240072611624213036139)
                    ·
                      rfl

theorem cell23_1713249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_1713249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713249 prefixEnd_1713249 := by exact prefixLift 1713249
  have htrace : WordTrace (prefixWord ++ tailWord_1713249) baseStart_1713249 baseEnd_1713249 := by
    simpa [prefixWord, tailWord_1713249, baseEnd_1713249] using wordTrace_append hprefix tailTrace_1713249
  have hstable : (prefixWord ++ tailWord_1713249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713249).length < 2 ^ (prefixWord ++ tailWord_1713249).sum := by decide
  have hdescent : baseEnd_1713249 < baseStart_1713249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713280 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 1, 1, 3]
def baseStart_1713280 : Nat := 118140960795 + 1713280 * 2 ^ 59
def prefixEnd_1713280 : Nat := 4983230072969 + 3 ^ 40 * 1713280 * 2
def baseEnd_1713280 : Nat := 879736135735162017820775

theorem tailTrace_1713280 : CollatzResearch.WordTrace tailWord_1713280 prefixEnd_1713280 879736135735162017820775 := by
  unfold tailWord_1713280
  simp only [CollatzResearch.WordTrace]
  refine ⟨31244227616543319886820647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41658970155391093182427529 31244227616543319886820647)
  ·
    refine ⟨46866341424814979830230971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31244227616543319886820647 46866341424814979830230971)
    ·
      refine ⟨70299512137222469745346457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46866341424814979830230971 70299512137222469745346457)
      ·
        refine ⟨52724634102916852309009843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70299512137222469745346457 52724634102916852309009843)
        ·
          refine ⟨79086951154375278463514765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52724634102916852309009843 79086951154375278463514765)
          ·
            refine ⟨29657606682890729423818037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79086951154375278463514765 29657606682890729423818037)
            ·
              refine ⟨2780400626521005883482941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29657606682890729423818037 2780400626521005883482941)
              ·
                refine ⟨1042650234945377206306103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2780400626521005883482941 1042650234945377206306103)
                ·
                  refine ⟨1563975352418065809459155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042650234945377206306103 1563975352418065809459155)
                  ·
                    refine ⟨2345963028627098714188733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1563975352418065809459155 2345963028627098714188733)
                    ·
                      refine ⟨879736135735162017820775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2345963028627098714188733 879736135735162017820775)
                      ·
                        rfl

theorem cell23_1713280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_1713280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713280 prefixEnd_1713280 := by exact prefixLift 1713280
  have htrace : WordTrace (prefixWord ++ tailWord_1713280) baseStart_1713280 baseEnd_1713280 := by
    simpa [prefixWord, tailWord_1713280, baseEnd_1713280] using wordTrace_append hprefix tailTrace_1713280
  have hstable : (prefixWord ++ tailWord_1713280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713280).length < 2 ^ (prefixWord ++ tailWord_1713280).sum := by decide
  have hdescent : baseEnd_1713280 < baseStart_1713280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713299 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6]
def baseStart_1713299 : Nat := 118140960795 + 1713299 * 2 ^ 59
def prefixEnd_1713299 : Nat := 4983230072969 + 3 ^ 40 * 1713299 * 2
def baseEnd_1713299 : Nat := 879745891867597443483187

theorem tailTrace_1713299 : CollatzResearch.WordTrace tailWord_1713299 prefixEnd_1713299 879745891867597443483187 := by
  unfold tailWord_1713299
  simp only [CollatzResearch.WordTrace]
  refine ⟨62489148220017806018582951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41659432146678537345721967 62489148220017806018582951)
  ·
    refine ⟨93733722330026709027874427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62489148220017806018582951 93733722330026709027874427)
    ·
      refine ⟨140600583495040063541811641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93733722330026709027874427 140600583495040063541811641)
      ·
        refine ⟨105450437621280047656358731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140600583495040063541811641 105450437621280047656358731)
        ·
          refine ⟨158175656431920071484538097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105450437621280047656358731 158175656431920071484538097)
          ·
            refine ⟨118631742323940053613403573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158175656431920071484538097 118631742323940053613403573)
            ·
              refine ⟨11121725842869380026256585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118631742323940053613403573 11121725842869380026256585)
              ·
                refine ⟨8341294382152035019692439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11121725842869380026256585 8341294382152035019692439)
                ·
                  refine ⟨12511941573228052529538659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341294382152035019692439 12511941573228052529538659)
                  ·
                    refine ⟨18767912359842078794307989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12511941573228052529538659 18767912359842078794307989)
                    ·
                      refine ⟨879745891867597443483187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18767912359842078794307989 879745891867597443483187)
                      ·
                        rfl

theorem cell23_1713299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 6].length) (baseStart_1713299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713299 prefixEnd_1713299 := by exact prefixLift 1713299
  have htrace : WordTrace (prefixWord ++ tailWord_1713299) baseStart_1713299 baseEnd_1713299 := by
    simpa [prefixWord, tailWord_1713299, baseEnd_1713299] using wordTrace_append hprefix tailTrace_1713299
  have hstable : (prefixWord ++ tailWord_1713299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713299).length < 2 ^ (prefixWord ++ tailWord_1713299).sum := by decide
  have hdescent : baseEnd_1713299 < baseStart_1713299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713313 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 2, 4]
def baseStart_1713313 : Nat := 118140960795 + 1713313 * 2 ^ 59
def prefixEnd_1713313 : Nat := 4983230072969 + 3 ^ 40 * 1713313 * 2
def baseEnd_1713313 : Nat := 293251026865586796236041

theorem tailTrace_1713313 : CollatzResearch.WordTrace tailWord_1713313 prefixEnd_1713313 293251026865586796236041 := by
  unfold tailWord_1713313
  simp only [CollatzResearch.WordTrace]
  refine ⟨62489658841967086409592593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41659772561311390939728395 62489658841967086409592593)
  ·
    refine ⟨46867244131475314807194445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62489658841967086409592593 46867244131475314807194445)
    ·
      refine ⟨17575216549303243052697917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46867244131475314807194445 17575216549303243052697917)
      ·
        refine ⟨6590706205988716144761719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17575216549303243052697917 6590706205988716144761719)
        ·
          refine ⟨9886059308983074217142579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6590706205988716144761719 9886059308983074217142579)
          ·
            refine ⟨14829088963474611325713869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9886059308983074217142579 14829088963474611325713869)
            ·
              refine ⟨5560908361302979247142701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14829088963474611325713869 5560908361302979247142701)
              ·
                refine ⟨2085340635488617217678513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5560908361302979247142701 2085340635488617217678513)
                ·
                  refine ⟨1564005476616462913258885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085340635488617217678513 1564005476616462913258885)
                  ·
                    refine ⟨293251026865586796236041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1564005476616462913258885 293251026865586796236041)
                    ·
                      rfl

theorem cell23_1713313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_1713313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713313 prefixEnd_1713313 := by exact prefixLift 1713313
  have htrace : WordTrace (prefixWord ++ tailWord_1713313) baseStart_1713313 baseEnd_1713313 := by
    simpa [prefixWord, tailWord_1713313, baseEnd_1713313] using wordTrace_append hprefix tailTrace_1713313
  have hstable : (prefixWord ++ tailWord_1713313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713313).length < 2 ^ (prefixWord ++ tailWord_1713313).sum := by decide
  have hdescent : baseEnd_1713313 < baseStart_1713313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713316 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_1713316 : Nat := 118140960795 + 1713316 * 2 ^ 59
def prefixEnd_1713316 : Nat := 4983230072969 + 3 ^ 40 * 1713316 * 2
def baseEnd_1713316 : Nat := 879754621038723876970609

theorem tailTrace_1713316 : CollatzResearch.WordTrace tailWord_1713316 prefixEnd_1713316 879754621038723876970609 := by
  unfold tailWord_1713316
  simp only [CollatzResearch.WordTrace]
  refine ⟨31244884130478108960975901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41659845507304145281301201 31244884130478108960975901)
  ·
    refine ⟨11716831548929290860365963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31244884130478108960975901 11716831548929290860365963)
    ·
      refine ⟨17575247323393936290548945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11716831548929290860365963 17575247323393936290548945)
      ·
        refine ⟨13181435492545452217911709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17575247323393936290548945 13181435492545452217911709)
        ·
          refine ⟨4943038309704544581716891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13181435492545452217911709 4943038309704544581716891)
          ·
            refine ⟨7414557464556816872575337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943038309704544581716891 7414557464556816872575337)
            ·
              refine ⟨5560918098417612654431503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7414557464556816872575337 5560918098417612654431503)
              ·
                refine ⟨8341377147626418981647255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5560918098417612654431503 8341377147626418981647255)
                ·
                  refine ⟨12512065721439628472470883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341377147626418981647255 12512065721439628472470883)
                  ·
                    refine ⟨18768098582159442708706325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12512065721439628472470883 18768098582159442708706325)
                    ·
                      refine ⟨879754621038723876970609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18768098582159442708706325 879754621038723876970609)
                      ·
                        rfl

theorem cell23_1713316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_1713316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713316 prefixEnd_1713316 := by exact prefixLift 1713316
  have htrace : WordTrace (prefixWord ++ tailWord_1713316) baseStart_1713316 baseEnd_1713316 := by
    simpa [prefixWord, tailWord_1713316, baseEnd_1713316] using wordTrace_append hprefix tailTrace_1713316
  have hstable : (prefixWord ++ tailWord_1713316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713316).length < 2 ^ (prefixWord ++ tailWord_1713316).sum := by decide
  have hdescent : baseEnd_1713316 < baseStart_1713316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713334 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_1713334 : Nat := 118140960795 + 1713334 * 2 ^ 59
def prefixEnd_1713334 : Nat := 4983230072969 + 3 ^ 40 * 1713334 * 2
def baseEnd_1713334 : Nat := 293254621230168268848509

theorem tailTrace_1713334 : CollatzResearch.WordTrace tailWord_1713334 prefixEnd_1713334 293254621230168268848509 := by
  unfold tailWord_1713334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3905651548430687937256691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41660283183260671330738037 3905651548430687937256691)
  ·
    refine ⟨5858477322646031905885037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3905651548430687937256691 5858477322646031905885037)
    ·
      refine ⟨2196928995992261964706889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5858477322646031905885037 2196928995992261964706889)
      ·
        refine ⟨1647696746994196473530167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2196928995992261964706889 1647696746994196473530167)
        ·
          refine ⟨2471545120491294710295251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647696746994196473530167 2471545120491294710295251)
          ·
            refine ⟨3707317680736942065442877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471545120491294710295251 3707317680736942065442877)
            ·
              refine ⟨1390244130276353274541079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3707317680736942065442877 1390244130276353274541079)
              ·
                refine ⟨2085366195414529911811619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390244130276353274541079 2085366195414529911811619)
                ·
                  refine ⟨3128049293121794867717429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085366195414529911811619 3128049293121794867717429)
                  ·
                    refine ⟨293254621230168268848509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3128049293121794867717429 293254621230168268848509)
                    ·
                      rfl

theorem cell23_1713334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_1713334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713334 prefixEnd_1713334 := by exact prefixLift 1713334
  have htrace : WordTrace (prefixWord ++ tailWord_1713334) baseStart_1713334 baseEnd_1713334 := by
    simpa [prefixWord, tailWord_1713334, baseEnd_1713334] using wordTrace_append hprefix tailTrace_1713334
  have hstable : (prefixWord ++ tailWord_1713334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713334).length < 2 ^ (prefixWord ++ tailWord_1713334).sum := by decide
  have hdescent : baseEnd_1713334 < baseStart_1713334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713354 : List Nat := [3, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2]
def baseStart_1713354 : Nat := 118140960795 + 1713354 * 2 ^ 59
def prefixEnd_1713354 : Nat := 4983230072969 + 3 ^ 40 * 1713354 * 2
def baseEnd_1713354 : Nat := 879774133303594728295435

theorem tailTrace_1713354 : CollatzResearch.WordTrace tailWord_1713354 prefixEnd_1713354 879774133303594728295435 := by
  unfold tailWord_1713354
  simp only [CollatzResearch.WordTrace]
  refine ⟨15622788558704637602958779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41660769489879033607890077 15622788558704637602958779)
  ·
    refine ⟨23434182838056956404438169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15622788558704637602958779 23434182838056956404438169)
    ·
      refine ⟨17575637128542717303328627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23434182838056956404438169 17575637128542717303328627)
      ·
        refine ⟨26363455692814075954992941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17575637128542717303328627 26363455692814075954992941)
        ·
          refine ⟨9886295884805278483122353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26363455692814075954992941 9886295884805278483122353)
          ·
            refine ⟨7414721913603958862341765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9886295884805278483122353 7414721913603958862341765)
            ·
              refine ⟨1390260358800742286689081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7414721913603958862341765 1390260358800742286689081)
              ·
                refine ⟨1042695269100556715016811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390260358800742286689081 1042695269100556715016811)
                ·
                  refine ⟨1564042903650835072525217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042695269100556715016811 1564042903650835072525217)
                  ·
                    refine ⟨1173032177738126304393913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564042903650835072525217 1173032177738126304393913)
                    ·
                      refine ⟨879774133303594728295435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173032177738126304393913 879774133303594728295435)
                      ·
                        rfl

theorem cell23_1713354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 2, 1, 2, 2].length) (baseStart_1713354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713354 prefixEnd_1713354 := by exact prefixLift 1713354
  have htrace : WordTrace (prefixWord ++ tailWord_1713354) baseStart_1713354 baseEnd_1713354 := by
    simpa [prefixWord, tailWord_1713354, baseEnd_1713354] using wordTrace_append hprefix tailTrace_1713354
  have hstable : (prefixWord ++ tailWord_1713354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713354).length < 2 ^ (prefixWord ++ tailWord_1713354).sum := by decide
  have hdescent : baseEnd_1713354 < baseStart_1713354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713404 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_1713404 : Nat := 118140960795 + 1713404 * 2 ^ 59
def prefixEnd_1713404 : Nat := 4983230072969 + 3 ^ 40 * 1713404 * 2
def baseEnd_1713404 : Nat := 879799807336319532670205

theorem tailTrace_1713404 : CollatzResearch.WordTrace tailWord_1713404 prefixEnd_1713404 879799807336319532670205 := by
  unfold tailWord_1713404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31246488942318704475577633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41661985256424939300770177 31246488942318704475577633)
  ·
    refine ⟨23434866706739028356683225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31246488942318704475577633 23434866706739028356683225)
    ·
      refine ⟨17576150030054271267512419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23434866706739028356683225 17576150030054271267512419)
      ·
        refine ⟨26364225045081406901268629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17576150030054271267512419 26364225045081406901268629)
        ·
          refine ⟨1235823048988190948496967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26364225045081406901268629 1235823048988190948496967)
          ·
            refine ⟨1853734573482286422745451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235823048988190948496967 1853734573482286422745451)
            ·
              refine ⟨2780601860223429634118177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853734573482286422745451 2780601860223429634118177)
              ·
                refine ⟨2085451395167572225588633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780601860223429634118177 2085451395167572225588633)
                ·
                  refine ⟨1564088546375679169191475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085451395167572225588633 1564088546375679169191475)
                  ·
                    refine ⟨2346132819563518753787213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1564088546375679169191475 2346132819563518753787213)
                    ·
                      refine ⟨879799807336319532670205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2346132819563518753787213 879799807336319532670205)
                      ·
                        rfl

theorem cell23_1713404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_1713404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713404 prefixEnd_1713404 := by exact prefixLift 1713404
  have htrace : WordTrace (prefixWord ++ tailWord_1713404) baseStart_1713404 baseEnd_1713404 := by
    simpa [prefixWord, tailWord_1713404, baseEnd_1713404] using wordTrace_append hprefix tailTrace_1713404
  have hstable : (prefixWord ++ tailWord_1713404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713404).length < 2 ^ (prefixWord ++ tailWord_1713404).sum := by decide
  have hdescent : baseEnd_1713404 < baseStart_1713404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713456 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_1713456 : Nat := 118140960795 + 1713456 * 2 ^ 59
def prefixEnd_1713456 : Nat := 4983230072969 + 3 ^ 40 * 1713456 * 2
def baseEnd_1713456 : Nat := 879826508330353329219965

theorem tailTrace_1713456 : CollatzResearch.WordTrace tailWord_1713456 prefixEnd_1713456 879826508330353329219965 := by
  unfold tailWord_1713456
  simp only [CollatzResearch.WordTrace]
  refine ⟨31247437240224510916024111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41663249653632681221365481 31247437240224510916024111)
  ·
    refine ⟨46871155860336766374036167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31247437240224510916024111 46871155860336766374036167)
    ·
      refine ⟨70306733790505149561054251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46871155860336766374036167 70306733790505149561054251)
      ·
        refine ⟨105460100685757724341581377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70306733790505149561054251 105460100685757724341581377)
        ·
          refine ⟨79095075514318293256186033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105460100685757724341581377 79095075514318293256186033)
          ·
            refine ⟨59321306635738719942139525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79095075514318293256186033 59321306635738719942139525)
            ·
              refine ⟨11122744994201009989151161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59321306635738719942139525 11122744994201009989151161)
              ·
                refine ⟨8342058745650757491863371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11122744994201009989151161 8342058745650757491863371)
                ·
                  refine ⟨12513088118476136237795057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8342058745650757491863371 12513088118476136237795057)
                  ·
                    refine ⟨9384816088857102178346293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12513088118476136237795057 9384816088857102178346293)
                    ·
                      refine ⟨879826508330353329219965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9384816088857102178346293 879826508330353329219965)
                      ·
                        rfl

theorem cell23_1713456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_1713456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713456 prefixEnd_1713456 := by exact prefixLift 1713456
  have htrace : WordTrace (prefixWord ++ tailWord_1713456) baseStart_1713456 baseEnd_1713456 := by
    simpa [prefixWord, tailWord_1713456, baseEnd_1713456] using wordTrace_append hprefix tailTrace_1713456
  have hstable : (prefixWord ++ tailWord_1713456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713456).length < 2 ^ (prefixWord ++ tailWord_1713456).sum := by decide
  have hdescent : baseEnd_1713456 < baseStart_1713456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713470 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_1713470 : Nat := 118140960795 + 1713470 * 2 ^ 59
def prefixEnd_1713470 : Nat := 4983230072969 + 3 ^ 40 * 1713470 * 2
def baseEnd_1713470 : Nat := 879833697059516274444901

theorem tailTrace_1713470 : CollatzResearch.WordTrace tailWord_1713470 prefixEnd_1713470 879833697059516274444901 := by
  unfold tailWord_1713470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811923137799787777882233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41663590068265534815371909 7811923137799787777882233)
  ·
    refine ⟨5858942353349840833411675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7811923137799787777882233 5858942353349840833411675)
    ·
      refine ⟨8788413530024761250117513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858942353349840833411675 8788413530024761250117513)
      ·
        refine ⟨6591310147518570937588135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8788413530024761250117513 6591310147518570937588135)
        ·
          refine ⟨9886965221277856406382203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591310147518570937588135 9886965221277856406382203)
          ·
            refine ⟨14830447831916784609573305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9886965221277856406382203 14830447831916784609573305)
            ·
              refine ⟨11122835873937588457179979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14830447831916784609573305 11122835873937588457179979)
              ·
                refine ⟨16684253810906382685769969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11122835873937588457179979 16684253810906382685769969)
                ·
                  refine ⟨12513190358179787014327477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16684253810906382685769969 12513190358179787014327477)
                  ·
                    refine ⟨1173111596079355032593201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12513190358179787014327477 1173111596079355032593201)
                    ·
                      refine ⟨879833697059516274444901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173111596079355032593201 879833697059516274444901)
                      ·
                        rfl

theorem cell23_1713470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_1713470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713470 prefixEnd_1713470 := by exact prefixLift 1713470
  have htrace : WordTrace (prefixWord ++ tailWord_1713470) baseStart_1713470 baseEnd_1713470 := by
    simpa [prefixWord, tailWord_1713470, baseEnd_1713470] using wordTrace_append hprefix tailTrace_1713470
  have hstable : (prefixWord ++ tailWord_1713470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713470).length < 2 ^ (prefixWord ++ tailWord_1713470).sum := by decide
  have hdescent : baseEnd_1713470 < baseStart_1713470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713473 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_1713473 : Nat := 118140960795 + 1713473 * 2 ^ 59
def prefixEnd_1713473 : Nat := 4983230072969 + 3 ^ 40 * 1713473 * 2
def baseEnd_1713473 : Nat := 879835237501479762707387

theorem tailTrace_1713473 : CollatzResearch.WordTrace tailWord_1713473 prefixEnd_1713473 879835237501479762707387 := by
  unfold tailWord_1713473
  simp only [CollatzResearch.WordTrace]
  refine ⟨62495494521387433735417073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41663663014258289156944715 62495494521387433735417073)
  ·
    refine ⟨46871620891040575301562805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62495494521387433735417073 46871620891040575301562805)
    ·
      refine ⟨4394214458535053934521513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46871620891040575301562805 4394214458535053934521513)
      ·
        refine ⟨3295660843901290450891135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4394214458535053934521513 3295660843901290450891135)
        ·
          refine ⟨4943491265851935676336703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295660843901290450891135 4943491265851935676336703)
          ·
            refine ⟨7415236898777903514505055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943491265851935676336703 7415236898777903514505055)
            ·
              refine ⟨11122855348166855271757583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415236898777903514505055 11122855348166855271757583)
              ·
                refine ⟨16684283022250282907636375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11122855348166855271757583 16684283022250282907636375)
                ·
                  refine ⟨25026424533375424361454563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16684283022250282907636375 25026424533375424361454563)
                  ·
                    refine ⟨37539636800063136542181845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25026424533375424361454563 37539636800063136542181845)
                    ·
                      refine ⟨879835237501479762707387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37539636800063136542181845 879835237501479762707387)
                      ·
                        rfl

theorem cell23_1713473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_1713473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713473 prefixEnd_1713473 := by exact prefixLift 1713473
  have htrace : WordTrace (prefixWord ++ tailWord_1713473) baseStart_1713473 baseEnd_1713473 := by
    simpa [prefixWord, tailWord_1713473, baseEnd_1713473] using wordTrace_append hprefix tailTrace_1713473
  have hstable : (prefixWord ++ tailWord_1713473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713473).length < 2 ^ (prefixWord ++ tailWord_1713473).sum := by decide
  have hdescent : baseEnd_1713473 < baseStart_1713473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713478 : List Nat := [6, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1713478 : Nat := 118140960795 + 1713478 * 2 ^ 59
def prefixEnd_1713478 : Nat := 4983230072969 + 3 ^ 40 * 1713478 * 2
def baseEnd_1713478 : Nat := 879837804904752243144865

theorem tailTrace_1713478 : CollatzResearch.WordTrace tailWord_1713478 prefixEnd_1713478 879837804904752243144865 := by
  unfold tailWord_1713478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1952989902699041237167159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41663784590912879726232725 1952989902699041237167159)
  ·
    refine ⟨2929484854048561855750739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1952989902699041237167159 2929484854048561855750739)
    ·
      refine ⟨4394227281072842783626109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2929484854048561855750739 4394227281072842783626109)
      ·
        refine ⟨1647835230402316043859791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4394227281072842783626109 1647835230402316043859791)
        ·
          refine ⟨2471752845603474065789687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647835230402316043859791 2471752845603474065789687)
          ·
            refine ⟨3707629268405211098684531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2471752845603474065789687 3707629268405211098684531)
            ·
              refine ⟨5561443902607816648026797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707629268405211098684531 5561443902607816648026797)
              ·
                refine ⟨2085541463477931243010049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5561443902607816648026797 2085541463477931243010049)
                ·
                  refine ⟨1564156097608448432257537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085541463477931243010049 1564156097608448432257537)
                  ·
                    refine ⟨1173117073206336324193153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564156097608448432257537 1173117073206336324193153)
                    ·
                      refine ⟨879837804904752243144865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173117073206336324193153 879837804904752243144865)
                      ·
                        rfl

theorem cell23_1713478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1713478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713478 prefixEnd_1713478 := by exact prefixLift 1713478
  have htrace : WordTrace (prefixWord ++ tailWord_1713478) baseStart_1713478 baseEnd_1713478 := by
    simpa [prefixWord, tailWord_1713478, baseEnd_1713478] using wordTrace_append hprefix tailTrace_1713478
  have hstable : (prefixWord ++ tailWord_1713478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713478).length < 2 ^ (prefixWord ++ tailWord_1713478).sum := by decide
  have hdescent : baseEnd_1713478 < baseStart_1713478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713483 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 6, 4, 2]
def baseStart_1713483 : Nat := 118140960795 + 1713483 * 2 ^ 59
def prefixEnd_1713483 : Nat := 4983230072969 + 3 ^ 40 * 1713483 * 2
def baseEnd_1713483 : Nat := 879840372308024723582341

theorem tailTrace_1713483 : CollatzResearch.WordTrace tailWord_1713483 prefixEnd_1713483 879840372308024723582341 := by
  unfold tailWord_1713483
  simp only [CollatzResearch.WordTrace]
  refine ⟨62495859251351205443281103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41663906167567470295520735 62495859251351205443281103)
  ·
    refine ⟨93743788877026808164921655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62495859251351205443281103 93743788877026808164921655)
    ·
      refine ⟨140615683315540212247382483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93743788877026808164921655 140615683315540212247382483)
      ·
        refine ⟨210923524973310318371073725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140615683315540212247382483 210923524973310318371073725)
        ·
          refine ⟨79096321864991369389152647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210923524973310318371073725 79096321864991369389152647)
          ·
            refine ⟨118644482797487054083728971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79096321864991369389152647 118644482797487054083728971)
            ·
              refine ⟨177966724196230581125593457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118644482797487054083728971 177966724196230581125593457)
              ·
                refine ⟨133475043147172935844195093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177966724196230581125593457 133475043147172935844195093)
                ·
                  refine ⟨6256642647523731367696645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133475043147172935844195093 6256642647523731367696645)
                  ·
                    refine ⟨1173120496410699631443121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6256642647523731367696645 1173120496410699631443121)
                    ·
                      refine ⟨879840372308024723582341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173120496410699631443121 879840372308024723582341)
                      ·
                        rfl

theorem cell23_1713483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 6, 4, 2].length) (baseStart_1713483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713483 prefixEnd_1713483 := by exact prefixLift 1713483
  have htrace : WordTrace (prefixWord ++ tailWord_1713483) baseStart_1713483 baseEnd_1713483 := by
    simpa [prefixWord, tailWord_1713483, baseEnd_1713483] using wordTrace_append hprefix tailTrace_1713483
  have hstable : (prefixWord ++ tailWord_1713483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713483).length < 2 ^ (prefixWord ++ tailWord_1713483).sum := by decide
  have hdescent : baseEnd_1713483 < baseStart_1713483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713573 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1713573 : Nat := 118140960795 + 1713573 * 2 ^ 59
def prefixEnd_1713573 : Nat := 4983230072969 + 3 ^ 40 * 1713573 * 2
def baseEnd_1713573 : Nat := 879886585566929371456927

theorem tailTrace_1713573 : CollatzResearch.WordTrace tailWord_1713573 prefixEnd_1713573 879886585566929371456927 := by
  unfold tailWord_1713573
  simp only [CollatzResearch.WordTrace]
  refine ⟨62499141821025150814057373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41666094547350100542704915 62499141821025150814057373)
  ·
    refine ⟨23437178182884431555271515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62499141821025150814057373 23437178182884431555271515)
    ·
      refine ⟨35155767274326647332907273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23437178182884431555271515 35155767274326647332907273)
      ·
        refine ⟨26366825455744985499680455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35155767274326647332907273 26366825455744985499680455)
        ·
          refine ⟨39550238183617478249520683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26366825455744985499680455 39550238183617478249520683)
          ·
            refine ⟨59325357275426217374281025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39550238183617478249520683 59325357275426217374281025)
            ·
              refine ⟨44494017956569663030710769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59325357275426217374281025 44494017956569663030710769)
              ·
                refine ⟨33370513467427247273033077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44494017956569663030710769 33370513467427247273033077)
                ·
                  refine ⟨3128485637571304431846851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33370513467427247273033077 3128485637571304431846851)
                  ·
                    refine ⟨4692728456356956647770277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3128485637571304431846851 4692728456356956647770277)
                    ·
                      refine ⟨879886585566929371456927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4692728456356956647770277 879886585566929371456927)
                      ·
                        rfl

theorem cell23_1713573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1713573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713573 prefixEnd_1713573 := by exact prefixLift 1713573
  have htrace : WordTrace (prefixWord ++ tailWord_1713573) baseStart_1713573 baseEnd_1713573 := by
    simpa [prefixWord, tailWord_1713573, baseEnd_1713573] using wordTrace_append hprefix tailTrace_1713573
  have hstable : (prefixWord ++ tailWord_1713573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713573).length < 2 ^ (prefixWord ++ tailWord_1713573).sum := by decide
  have hdescent : baseEnd_1713573 < baseStart_1713573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713600 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_1713600 : Nat := 118140960795 + 1713600 * 2 ^ 59
def prefixEnd_1713600 : Nat := 4983230072969 + 3 ^ 40 * 1713600 * 2
def baseEnd_1713600 : Nat := 293300149848200255273101

theorem tailTrace_1713600 : CollatzResearch.WordTrace tailWord_1713600 prefixEnd_1713600 293300149848200255273101 := by
  unfold tailWord_1713600
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250063295963667212645127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41666751061284889616860169 31250063295963667212645127)
  ·
    refine ⟨46875094943945500818967691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31250063295963667212645127 46875094943945500818967691)
    ·
      refine ⟨70312642415918251228451537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46875094943945500818967691 70312642415918251228451537)
      ·
        refine ⟨52734481811938688421338653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70312642415918251228451537 52734481811938688421338653)
        ·
          refine ⟨19775430679477008158001995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52734481811938688421338653 19775430679477008158001995)
          ·
            refine ⟨29663146019215512237002993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19775430679477008158001995 29663146019215512237002993)
            ·
              refine ⟨22247359514411634177752245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29663146019215512237002993 22247359514411634177752245)
              ·
                refine ⟨2085689954476090704164273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22247359514411634177752245 2085689954476090704164273)
                ·
                  refine ⟨1564267465857068028123205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085689954476090704164273 1564267465857068028123205)
                  ·
                    refine ⟨293300149848200255273101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1564267465857068028123205 293300149848200255273101)
                    ·
                      rfl

theorem cell23_1713600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_1713600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713600 prefixEnd_1713600 := by exact prefixLift 1713600
  have htrace : WordTrace (prefixWord ++ tailWord_1713600) baseStart_1713600 baseEnd_1713600 := by
    simpa [prefixWord, tailWord_1713600, baseEnd_1713600] using wordTrace_append hprefix tailTrace_1713600
  have hstable : (prefixWord ++ tailWord_1713600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713600).length < 2 ^ (prefixWord ++ tailWord_1713600).sum := by decide
  have hdescent : baseEnd_1713600 < baseStart_1713600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713607 : List Nat := [1, 1, 4, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_1713607 : Nat := 118140960795 + 1713607 * 2 ^ 59
def prefixEnd_1713607 : Nat := 4983230072969 + 3 ^ 40 * 1713607 * 2
def baseEnd_1713607 : Nat := 879904043909182238431771

theorem tailTrace_1713607 : CollatzResearch.WordTrace tailWord_1713607 prefixEnd_1713607 879904043909182238431771 := by
  unfold tailWord_1713607
  simp only [CollatzResearch.WordTrace]
  refine ⟨62500381902901974620795075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41666921268601316413863383 62500381902901974620795075)
  ·
    refine ⟨93750572854352961931192613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62500381902901974620795075 93750572854352961931192613)
    ·
      refine ⟨17578232410191180362098615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93750572854352961931192613 17578232410191180362098615)
      ·
        refine ⟨26367348615286770543147923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17578232410191180362098615 26367348615286770543147923)
        ·
          refine ⟨39551022922930155814721885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26367348615286770543147923 39551022922930155814721885)
          ·
            refine ⟨14831633596098808430520707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39551022922930155814721885 14831633596098808430520707)
            ·
              refine ⟨22247450394148212645781061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14831633596098808430520707 22247450394148212645781061)
              ·
                refine ⟨4171396948902789871083949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22247450394148212645781061 4171396948902789871083949)
                ·
                  refine ⟨1564273855838546201656481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4171396948902789871083949 1564273855838546201656481)
                  ·
                    refine ⟨1173205391878909651242361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564273855838546201656481 1173205391878909651242361)
                    ·
                      refine ⟨879904043909182238431771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173205391878909651242361 879904043909182238431771)
                      ·
                        rfl

theorem cell23_1713607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_1713607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713607 prefixEnd_1713607 := by exact prefixLift 1713607
  have htrace : WordTrace (prefixWord ++ tailWord_1713607) baseStart_1713607 baseEnd_1713607 := by
    simpa [prefixWord, tailWord_1713607, baseEnd_1713607] using wordTrace_append hprefix tailTrace_1713607
  have hstable : (prefixWord ++ tailWord_1713607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713607).length < 2 ^ (prefixWord ++ tailWord_1713607).sum := by decide
  have hdescent : baseEnd_1713607 < baseStart_1713607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713663 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4]
def baseStart_1713663 : Nat := 118140960795 + 1713663 * 2 ^ 59
def prefixEnd_1713663 : Nat := 4983230072969 + 3 ^ 40 * 1713663 * 2
def baseEnd_1713663 : Nat := 879932798825834019331513

theorem tailTrace_1713663 : CollatzResearch.WordTrace tailWord_1713663 prefixEnd_1713663 879932798825834019331513 := by
  unfold tailWord_1713663
  simp only [CollatzResearch.WordTrace]
  refine ⟨62502424390699096184833643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41668282927132730789889095 62502424390699096184833643)
  ·
    refine ⟨93753636586048644277250465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62502424390699096184833643 93753636586048644277250465)
    ·
      refine ⟨70315227439536483207937849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93753636586048644277250465 70315227439536483207937849)
      ·
        refine ⟨52736420579652362405953387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70315227439536483207937849 52736420579652362405953387)
        ·
          refine ⟨79104630869478543608930081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52736420579652362405953387 79104630869478543608930081)
          ·
            refine ⟨59328473152108907706697561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79104630869478543608930081 59328473152108907706697561)
            ·
              refine ⟨44496354864081680780023171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59328473152108907706697561 44496354864081680780023171)
              ·
                refine ⟨66744532296122521170034757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44496354864081680780023171 66744532296122521170034757)
                ·
                  refine ⟨12514599805522972719381517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66744532296122521170034757 12514599805522972719381517)
                  ·
                    refine ⟨4692974927071114769768069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12514599805522972719381517 4692974927071114769768069)
                    ·
                      refine ⟨879932798825834019331513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4692974927071114769768069 879932798825834019331513)
                      ·
                        rfl

theorem cell23_1713663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_1713663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713663 prefixEnd_1713663 := by exact prefixLift 1713663
  have htrace : WordTrace (prefixWord ++ tailWord_1713663) baseStart_1713663 baseEnd_1713663 := by
    simpa [prefixWord, tailWord_1713663, baseEnd_1713663] using wordTrace_append hprefix tailTrace_1713663
  have hstable : (prefixWord ++ tailWord_1713663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713663).length < 2 ^ (prefixWord ++ tailWord_1713663).sum := by decide
  have hdescent : baseEnd_1713663 < baseStart_1713663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713667 : List Nat := [1, 1, 1, 3, 2, 1, 2, 6, 1, 3, 2]
def baseStart_1713667 : Nat := 118140960795 + 1713667 * 2 ^ 59
def prefixEnd_1713667 : Nat := 4983230072969 + 3 ^ 40 * 1713667 * 2
def baseEnd_1713667 : Nat := 879934852748452003681495

theorem tailTrace_1713667 : CollatzResearch.WordTrace tailWord_1713667 prefixEnd_1713667 879934852748452003681495 := by
  unfold tailWord_1713667
  simp only [CollatzResearch.WordTrace]
  refine ⟨62502570282684604867979255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41668380188456403245319503 62502570282684604867979255)
  ·
    refine ⟨93753855424026907301968883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62502570282684604867979255 93753855424026907301968883)
    ·
      refine ⟨140630783136040360952953325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93753855424026907301968883 140630783136040360952953325)
      ·
        refine ⟨52736543676015135357357497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140630783136040360952953325 52736543676015135357357497)
        ·
          refine ⟨39552407757011351518018123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52736543676015135357357497 39552407757011351518018123)
          ·
            refine ⟨59328611635517027277027185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39552407757011351518018123 59328611635517027277027185)
            ·
              refine ⟨44496458726637770457770389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59328611635517027277027185 44496458726637770457770389)
              ·
                refine ⟨2085771502811145490207987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44496458726637770457770389 2085771502811145490207987)
                ·
                  refine ⟨3128657254216718235311981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085771502811145490207987 3128657254216718235311981)
                  ·
                    refine ⟨1173246470331269338241993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3128657254216718235311981 1173246470331269338241993)
                    ·
                      refine ⟨879934852748452003681495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173246470331269338241993 879934852748452003681495)
                      ·
                        rfl

theorem cell23_1713667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_1713667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713667 prefixEnd_1713667 := by exact prefixLift 1713667
  have htrace : WordTrace (prefixWord ++ tailWord_1713667) baseStart_1713667 baseEnd_1713667 := by
    simpa [prefixWord, tailWord_1713667, baseEnd_1713667] using wordTrace_append hprefix tailTrace_1713667
  have hstable : (prefixWord ++ tailWord_1713667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713667).length < 2 ^ (prefixWord ++ tailWord_1713667).sum := by decide
  have hdescent : baseEnd_1713667 < baseStart_1713667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713720 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 7]
def baseStart_1713720 : Nat := 118140960795 + 1713720 * 2 ^ 59
def prefixEnd_1713720 : Nat := 4983230072969 + 3 ^ 40 * 1713720 * 2
def baseEnd_1713720 : Nat := 97773563024793366257639

theorem tailTrace_1713720 : CollatzResearch.WordTrace tailWord_1713720 prefixEnd_1713720 97773563024793366257639 := by
  unfold tailWord_1713720
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252251675746297459829307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41669668900995063279772409 31252251675746297459829307)
  ·
    refine ⟨46878377513619446189743961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31252251675746297459829307 46878377513619446189743961)
    ·
      refine ⟨35158783135214584642307971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46878377513619446189743961 35158783135214584642307971)
      ·
        refine ⟨52738174702821876963461957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35158783135214584642307971 52738174702821876963461957)
        ·
          refine ⟨9888407756779101930649117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52738174702821876963461957 9888407756779101930649117)
          ·
            refine ⟨3708152908792163223993419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9888407756779101930649117 3708152908792163223993419)
            ·
              refine ⟨5562229363188244835990129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708152908792163223993419 5562229363188244835990129)
              ·
                refine ⟨4171672022391183626992597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562229363188244835990129 4171672022391183626992597)
                ·
                  refine ⟨97773563024793366257639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4171672022391183626992597 97773563024793366257639)
                  ·
                    rfl

theorem cell23_1713720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_1713720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713720 prefixEnd_1713720 := by exact prefixLift 1713720
  have htrace : WordTrace (prefixWord ++ tailWord_1713720) baseStart_1713720 baseEnd_1713720 := by
    simpa [prefixWord, tailWord_1713720, baseEnd_1713720] using wordTrace_append hprefix tailTrace_1713720
  have hstable : (prefixWord ++ tailWord_1713720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713720).length < 2 ^ (prefixWord ++ tailWord_1713720).sum := by decide
  have hdescent : baseEnd_1713720 < baseStart_1713720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713864 : List Nat := [2, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_1713864 : Nat := 118140960795 + 1713864 * 2 ^ 59
def prefixEnd_1713864 : Nat := 4983230072969 + 3 ^ 40 * 1713864 * 2
def baseEnd_1713864 : Nat := 880036008437387732918089

theorem tailTrace_1713864 : CollatzResearch.WordTrace tailWord_1713864 prefixEnd_1713864 880036008437387732918089 := by
  unfold tailWord_1713864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31254877731485453756450323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41673170308647271675267097 31254877731485453756450323)
  ·
    refine ⟨46882316597228180634675485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31254877731485453756450323 46882316597228180634675485)
    ·
      refine ⟨17580868723960567738003307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46882316597228180634675485 17580868723960567738003307)
      ·
        refine ⟨26371303085940851607004961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17580868723960567738003307 26371303085940851607004961)
        ·
          refine ⟨19778477314455638705253721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26371303085940851607004961 19778477314455638705253721)
          ·
            refine ⟨14833857985841729028940291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19778477314455638705253721 14833857985841729028940291)
            ·
              refine ⟨22250786978762593543410437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14833857985841729028940291 22250786978762593543410437)
              ·
                refine ⟨4172022558517986289389457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22250786978762593543410437 4172022558517986289389457)
                ·
                  refine ⟨3129016918888489717042093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172022558517986289389457 3129016918888489717042093)
                  ·
                    refine ⟨1173381344583183643890785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3129016918888489717042093 1173381344583183643890785)
                    ·
                      refine ⟨880036008437387732918089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173381344583183643890785 880036008437387732918089)
                      ·
                        rfl

theorem cell23_1713864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_1713864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713864 prefixEnd_1713864 := by exact prefixLift 1713864
  have htrace : WordTrace (prefixWord ++ tailWord_1713864) baseStart_1713864 baseEnd_1713864 := by
    simpa [prefixWord, tailWord_1713864, baseEnd_1713864] using wordTrace_append hprefix tailTrace_1713864
  have hstable : (prefixWord ++ tailWord_1713864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713864).length < 2 ^ (prefixWord ++ tailWord_1713864).sum := by decide
  have hdescent : baseEnd_1713864 < baseStart_1713864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713887 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 1, 6]
def baseStart_1713887 : Nat := 118140960795 + 1713887 * 2 ^ 59
def prefixEnd_1713887 : Nat := 4983230072969 + 3 ^ 40 * 1713887 * 2
def baseEnd_1713887 : Nat := 293349272830813714310161

theorem tailTrace_1713887 : CollatzResearch.WordTrace tailWord_1713887 prefixEnd_1713887 293349272830813714310161 := by
  unfold tailWord_1713887
  simp only [CollatzResearch.WordTrace]
  refine ⟨62510594341887582440987915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41673729561258388293991943 62510594341887582440987915)
  ·
    refine ⟨93765891512831373661481873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62510594341887582440987915 93765891512831373661481873)
    ·
      refine ⟨70324418634623530246111405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93765891512831373661481873 70324418634623530246111405)
      ·
        refine ⟨26371656987983823842291777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70324418634623530246111405 26371656987983823842291777)
        ·
          refine ⟨19778742740987867881718833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26371656987983823842291777 19778742740987867881718833)
          ·
            refine ⟨14834057055740900911289125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19778742740987867881718833 14834057055740900911289125)
            ·
              refine ⟨2781385697951418920866711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14834057055740900911289125 2781385697951418920866711)
              ·
                refine ⟨4172078546927128381300067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781385697951418920866711 4172078546927128381300067)
                ·
                  refine ⟨6258117820390692571950101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172078546927128381300067 6258117820390692571950101)
                  ·
                    refine ⟨293349272830813714310161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6258117820390692571950101 293349272830813714310161)
                    ·
                      rfl

theorem cell23_1713887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 6].length) (baseStart_1713887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713887 prefixEnd_1713887 := by exact prefixLift 1713887
  have htrace : WordTrace (prefixWord ++ tailWord_1713887) baseStart_1713887 baseEnd_1713887 := by
    simpa [prefixWord, tailWord_1713887, baseEnd_1713887] using wordTrace_append hprefix tailTrace_1713887
  have hstable : (prefixWord ++ tailWord_1713887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713887).length < 2 ^ (prefixWord ++ tailWord_1713887).sum := by decide
  have hdescent : baseEnd_1713887 < baseStart_1713887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713900 : List Nat := [2, 2, 1, 1, 2, 2, 2, 11]
def baseStart_1713900 : Nat := 118140960795 + 1713900 * 2 ^ 59
def prefixEnd_1713900 : Nat := 4983230072969 + 3 ^ 40 * 1713900 * 2
def baseEnd_1713900 : Nat := 32594610879294429335849

theorem tailTrace_1713900 : CollatzResearch.WordTrace tailWord_1713900 prefixEnd_1713900 32594610879294429335849 := by
  unfold tailWord_1713900
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255534245420242830605577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41674045660560323774140769 31255534245420242830605577)
  ·
    refine ⟨23441650684065182122954183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31255534245420242830605577 23441650684065182122954183)
    ·
      refine ⟨35162476026097773184431275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23441650684065182122954183 35162476026097773184431275)
      ·
        refine ⟨52743714039146659776646913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35162476026097773184431275 52743714039146659776646913)
        ·
          refine ⟨39557785529359994832485185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52743714039146659776646913 39557785529359994832485185)
          ·
            refine ⟨29668339147019996124363889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39557785529359994832485185 29668339147019996124363889)
            ·
              refine ⟨22251254360264997093272917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29668339147019996124363889 22251254360264997093272917)
              ·
                refine ⟨32594610879294429335849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 22251254360264997093272917 32594610879294429335849)
                ·
                  rfl

theorem cell23_1713900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 11].length) (baseStart_1713900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713900 prefixEnd_1713900 := by exact prefixLift 1713900
  have htrace : WordTrace (prefixWord ++ tailWord_1713900) baseStart_1713900 baseEnd_1713900 := by
    simpa [prefixWord, tailWord_1713900, baseEnd_1713900] using wordTrace_append hprefix tailTrace_1713900
  have hstable : (prefixWord ++ tailWord_1713900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713900).length < 2 ^ (prefixWord ++ tailWord_1713900).sum := by decide
  have hdescent : baseEnd_1713900 < baseStart_1713900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713907 : List Nat := [1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4]
def baseStart_1713907 : Nat := 118140960795 + 1713907 * 2 ^ 59
def prefixEnd_1713907 : Nat := 4983230072969 + 3 ^ 40 * 1713907 * 2
def baseEnd_1713907 : Nat := 880058088105531064680391

theorem tailTrace_1713907 : CollatzResearch.WordTrace tailWord_1713907 prefixEnd_1713907 880058088105531064680391 := by
  unfold tailWord_1713907
  simp only [CollatzResearch.WordTrace]
  refine ⟨62511323801815125856715975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41674215867876750571143983 62511323801815125856715975)
  ·
    refine ⟨93766985702722688785073963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62511323801815125856715975 93766985702722688785073963)
    ·
      refine ⟨140650478554084033177610945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93766985702722688785073963 140650478554084033177610945)
      ·
        refine ⟨105487858915563024883208209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140650478554084033177610945 105487858915563024883208209)
        ·
          refine ⟨79115894186672268662406157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105487858915563024883208209 79115894186672268662406157)
          ·
            refine ⟨29668460320002100748402309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79115894186672268662406157 29668460320002100748402309)
            ·
              refine ⟨5562836310000393890325433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29668460320002100748402309 5562836310000393890325433)
              ·
                refine ⟨4172127232500295417744075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562836310000393890325433 4172127232500295417744075)
                ·
                  refine ⟨6258190848750443126616113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172127232500295417744075 6258190848750443126616113)
                  ·
                    refine ⟨4693643136562832344962085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6258190848750443126616113 4693643136562832344962085)
                    ·
                      refine ⟨880058088105531064680391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4693643136562832344962085 880058088105531064680391)
                      ·
                        rfl

theorem cell23_1713907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 4].length) (baseStart_1713907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713907 prefixEnd_1713907 := by exact prefixLift 1713907
  have htrace : WordTrace (prefixWord ++ tailWord_1713907) baseStart_1713907 baseEnd_1713907 := by
    simpa [prefixWord, tailWord_1713907, baseEnd_1713907] using wordTrace_append hprefix tailTrace_1713907
  have hstable : (prefixWord ++ tailWord_1713907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713907).length < 2 ^ (prefixWord ++ tailWord_1713907).sum := by decide
  have hdescent : baseEnd_1713907 < baseStart_1713907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713908 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1713908 : Nat := 118140960795 + 1713908 * 2 ^ 59
def prefixEnd_1713908 : Nat := 4983230072969 + 3 ^ 40 * 1713908 * 2
def baseEnd_1713908 : Nat := 293352867195395186922629

theorem tailTrace_1713908 : CollatzResearch.WordTrace tailWord_1713908 prefixEnd_1713908 293352867195395186922629 := by
  unfold tailWord_1713908
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255680137405751513751189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41674240183207668685001585 31255680137405751513751189)
  ·
    refine ⟨1465110006440894602207087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31255680137405751513751189 1465110006440894602207087)
    ·
      refine ⟨2197665009661341903310631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465110006440894602207087 2197665009661341903310631)
      ·
        refine ⟨3296497514492012854965947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197665009661341903310631 3296497514492012854965947)
        ·
          refine ⟨4944746271738019282448921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296497514492012854965947 4944746271738019282448921)
          ·
            refine ⟨3708559703803514461836691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944746271738019282448921 3708559703803514461836691)
            ·
              refine ⟨5562839555705271692755037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708559703803514461836691 5562839555705271692755037)
              ·
                refine ⟨2086064833389476884783139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5562839555705271692755037 2086064833389476884783139)
                ·
                  refine ⟨3129097250084215327174709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086064833389476884783139 3129097250084215327174709)
                  ·
                    refine ⟨293352867195395186922629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3129097250084215327174709 293352867195395186922629)
                    ·
                      rfl

theorem cell23_1713908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1713908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713908 prefixEnd_1713908 := by exact prefixLift 1713908
  have htrace : WordTrace (prefixWord ++ tailWord_1713908) baseStart_1713908 baseEnd_1713908 := by
    simpa [prefixWord, tailWord_1713908, baseEnd_1713908] using wordTrace_append hprefix tailTrace_1713908
  have hstable : (prefixWord ++ tailWord_1713908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713908).length < 2 ^ (prefixWord ++ tailWord_1713908).sum := by decide
  have hdescent : baseEnd_1713908 < baseStart_1713908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713928 : List Nat := [2, 1, 3, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_1713928 : Nat := 118140960795 + 1713928 * 2 ^ 59
def prefixEnd_1713928 : Nat := 4983230072969 + 3 ^ 40 * 1713928 * 2
def baseEnd_1713928 : Nat := 880068871199275482517795

theorem tailTrace_1713928 : CollatzResearch.WordTrace tailWord_1713928 prefixEnd_1713928 880068871199275482517795 := by
  unfold tailWord_1713928
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256044867369523221615219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41674726489826030962153625 31256044867369523221615219)
  ·
    refine ⟨46884067301054284832422829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31256044867369523221615219 46884067301054284832422829)
    ·
      refine ⟨17581525237895356812158561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46884067301054284832422829 17581525237895356812158561)
      ·
        refine ⟨13186143928421517609118921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17581525237895356812158561 13186143928421517609118921)
        ·
          refine ⟨9889607946316138206839191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13186143928421517609118921 9889607946316138206839191)
          ·
            refine ⟨14834411919474207310258787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9889607946316138206839191 14834411919474207310258787)
            ·
              refine ⟨22251617879211310965388181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14834411919474207310258787 22251617879211310965388181)
              ·
                refine ⟨1043044588088030201502571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22251617879211310965388181 1043044588088030201502571)
                ·
                  refine ⟨1564566882132045302253857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043044588088030201502571 1564566882132045302253857)
                  ·
                    refine ⟨1173425161599033976690393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564566882132045302253857 1173425161599033976690393)
                    ·
                      refine ⟨880068871199275482517795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173425161599033976690393 880068871199275482517795)
                      ·
                        rfl

theorem cell23_1713928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_1713928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713928 prefixEnd_1713928 := by exact prefixLift 1713928
  have htrace : WordTrace (prefixWord ++ tailWord_1713928) baseStart_1713928 baseEnd_1713928 := by
    simpa [prefixWord, tailWord_1713928, baseEnd_1713928] using wordTrace_append hprefix tailTrace_1713928
  have hstable : (prefixWord ++ tailWord_1713928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713928).length < 2 ^ (prefixWord ++ tailWord_1713928).sum := by decide
  have hdescent : baseEnd_1713928 < baseStart_1713928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713944 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1713944 : Nat := 118140960795 + 1713944 * 2 ^ 59
def prefixEnd_1713944 : Nat := 4983230072969 + 3 ^ 40 * 1713944 * 2
def baseEnd_1713944 : Nat := 880077086889747419917721

theorem tailTrace_1713944 : CollatzResearch.WordTrace tailWord_1713944 prefixEnd_1713944 880077086889747419917721 := by
  unfold tailWord_1713944
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256336651340540587906443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41675115535120720783875257 31256336651340540587906443)
  ·
    refine ⟨46884504977010810881859665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31256336651340540587906443 46884504977010810881859665)
    ·
      refine ⟨35163378732758108161394749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46884504977010810881859665 35163378732758108161394749)
      ·
        refine ⟨13186267024784290560523031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35163378732758108161394749 13186267024784290560523031)
        ·
          refine ⟨19779400537176435840784547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13186267024784290560523031 19779400537176435840784547)
          ·
            refine ⟨29669100805764653761176821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19779400537176435840784547 29669100805764653761176821)
            ·
              refine ⟨2781478200540436290110327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29669100805764653761176821 2781478200540436290110327)
              ·
                refine ⟨4172217300810654435165491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781478200540436290110327 4172217300810654435165491)
                ·
                  refine ⟨6258325951215981652748237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172217300810654435165491 6258325951215981652748237)
                  ·
                    refine ⟨2346872231705993119780589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6258325951215981652748237 2346872231705993119780589)
                    ·
                      refine ⟨880077086889747419917721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2346872231705993119780589 880077086889747419917721)
                      ·
                        rfl

theorem cell23_1713944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1713944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713944 prefixEnd_1713944 := by exact prefixLift 1713944
  have htrace : WordTrace (prefixWord ++ tailWord_1713944) baseStart_1713944 baseEnd_1713944 := by
    simpa [prefixWord, tailWord_1713944, baseEnd_1713944] using wordTrace_append hprefix tailTrace_1713944
  have hstable : (prefixWord ++ tailWord_1713944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713944).length < 2 ^ (prefixWord ++ tailWord_1713944).sum := by decide
  have hdescent : baseEnd_1713944 < baseStart_1713944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713957 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1713957 : Nat := 118140960795 + 1713957 * 2 ^ 59
def prefixEnd_1713957 : Nat := 4983230072969 + 3 ^ 40 * 1713957 * 2
def baseEnd_1713957 : Nat := 880083762138255869055161

theorem tailTrace_1713957 : CollatzResearch.WordTrace tailWord_1713957 prefixEnd_1713957 880083762138255869055161 := by
  unfold tailWord_1713957
  simp only [CollatzResearch.WordTrace]
  refine ⟨62513147451633984396036125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41675431634422656264024083 62513147451633984396036125)
  ·
    refine ⟨23442430294362744148513547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62513147451633984396036125 23442430294362744148513547)
    ·
      refine ⟨35163645441544116222770321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442430294362744148513547 35163645441544116222770321)
      ·
        refine ⟨26372734081158087167077741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35163645441544116222770321 26372734081158087167077741)
        ·
          refine ⟨9889775280434282687654153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26372734081158087167077741 9889775280434282687654153)
          ·
            refine ⟨7417331460325712015740615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9889775280434282687654153 7417331460325712015740615)
            ·
              refine ⟨11125997190488568023610923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417331460325712015740615 11125997190488568023610923)
              ·
                refine ⟨16688995785732852035416385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11125997190488568023610923 16688995785732852035416385)
                ·
                  refine ⟨12516746839299639026562289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16688995785732852035416385 12516746839299639026562289)
                  ·
                    refine ⟨9387560129474729269921717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12516746839299639026562289 9387560129474729269921717)
                    ·
                      refine ⟨880083762138255869055161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9387560129474729269921717 880083762138255869055161)
                      ·
                        rfl

theorem cell23_1713957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1713957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1713957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1713957 prefixEnd_1713957 := by exact prefixLift 1713957
  have htrace : WordTrace (prefixWord ++ tailWord_1713957) baseStart_1713957 baseEnd_1713957 := by
    simpa [prefixWord, tailWord_1713957, baseEnd_1713957] using wordTrace_append hprefix tailTrace_1713957
  have hstable : (prefixWord ++ tailWord_1713957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713957).length < 2 ^ (prefixWord ++ tailWord_1713957).sum := by decide
  have hdescent : baseEnd_1713957 < baseStart_1713957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714004 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_1714004 : Nat := 118140960795 + 1714004 * 2 ^ 59
def prefixEnd_1714004 : Nat := 4983230072969 + 3 ^ 40 * 1714004 * 2
def baseEnd_1714004 : Nat := 880107895729017185167445

theorem tailTrace_1714004 : CollatzResearch.WordTrace tailWord_1714004 prefixEnd_1714004 880107895729017185167445 := by
  unfold tailWord_1714004
  simp only [CollatzResearch.WordTrace]
  refine ⟨31257430841231855711498533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41676574454975807615331377 31257430841231855711498533)
  ·
    refine ⟨5860768282730972945905975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31257430841231855711498533 5860768282730972945905975)
    ·
      refine ⟨8791152424096459418858963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5860768282730972945905975 8791152424096459418858963)
      ·
        refine ⟨13186728636144689128288445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8791152424096459418858963 13186728636144689128288445)
        ·
          refine ⟨4945023238554258423108167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13186728636144689128288445 4945023238554258423108167)
          ·
            refine ⟨7417534857831387634662251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945023238554258423108167 7417534857831387634662251)
            ·
              refine ⟨11126302286747081451993377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417534857831387634662251 11126302286747081451993377)
              ·
                refine ⟨8344726715060311088995033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11126302286747081451993377 8344726715060311088995033)
                ·
                  refine ⟨6258545036295233316746275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344726715060311088995033 6258545036295233316746275)
                  ·
                    refine ⟨9387817554442849975119413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6258545036295233316746275 9387817554442849975119413)
                    ·
                      refine ⟨880107895729017185167445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9387817554442849975119413 880107895729017185167445)
                      ·
                        rfl

theorem cell23_1714004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_1714004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714004 prefixEnd_1714004 := by exact prefixLift 1714004
  have htrace : WordTrace (prefixWord ++ tailWord_1714004) baseStart_1714004 baseEnd_1714004 := by
    simpa [prefixWord, tailWord_1714004, baseEnd_1714004] using wordTrace_append hprefix tailTrace_1714004
  have hstable : (prefixWord ++ tailWord_1714004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714004).length < 2 ^ (prefixWord ++ tailWord_1714004).sum := by decide
  have hdescent : baseEnd_1714004 < baseStart_1714004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714018 : List Nat := [3, 3, 2, 1, 2, 2, 1, 2, 1, 4, 2]
def baseStart_1714018 : Nat := 118140960795 + 1714018 * 2 ^ 59
def prefixEnd_1714018 : Nat := 4983230072969 + 3 ^ 40 * 1714018 * 2
def baseEnd_1714018 : Nat := 880115084458180130392381

theorem tailTrace_1714018 : CollatzResearch.WordTrace tailWord_1714018 prefixEnd_1714018 880115084458180130392381 := by
  unfold tailWord_1714018
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628843076103247953501677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41676914869608661209337805 15628843076103247953501677)
  ·
    refine ⟨5860816153538717982563129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15628843076103247953501677 5860816153538717982563129)
    ·
      refine ⟨4395612115154038486922347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5860816153538717982563129 4395612115154038486922347)
      ·
        refine ⟨6593418172731057730383521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4395612115154038486922347 6593418172731057730383521)
        ·
          refine ⟨4945063629548293297787641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6593418172731057730383521 4945063629548293297787641)
          ·
            refine ⟨3708797722161219973340731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945063629548293297787641 3708797722161219973340731)
            ·
              refine ⟨5563196583241829960011097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708797722161219973340731 5563196583241829960011097)
              ·
                refine ⟨4172397437431372470008323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5563196583241829960011097 4172397437431372470008323)
                ·
                  refine ⟨6258596156147058705012485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172397437431372470008323 6258596156147058705012485)
                  ·
                    refine ⟨1173486779277573507189841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6258596156147058705012485 1173486779277573507189841)
                    ·
                      refine ⟨880115084458180130392381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173486779277573507189841 880115084458180130392381)
                      ·
                        rfl

theorem cell23_1714018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_1714018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714018 prefixEnd_1714018 := by exact prefixLift 1714018
  have htrace : WordTrace (prefixWord ++ tailWord_1714018) baseStart_1714018 baseEnd_1714018 := by
    simpa [prefixWord, tailWord_1714018, baseEnd_1714018] using wordTrace_append hprefix tailTrace_1714018
  have hstable : (prefixWord ++ tailWord_1714018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714018).length < 2 ^ (prefixWord ++ tailWord_1714018).sum := by decide
  have hdescent : baseEnd_1714018 < baseStart_1714018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714034 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1714034 : Nat := 118140960795 + 1714034 * 2 ^ 59
def prefixEnd_1714034 : Nat := 4983230072969 + 3 ^ 40 * 1714034 * 2
def baseEnd_1714034 : Nat := 880123300148652067792307

theorem tailTrace_1714034 : CollatzResearch.WordTrace tailWord_1714034 prefixEnd_1714034 880123300148652067792307 := by
  unfold tailWord_1714034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628988968088756636647289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41677303914903351031059437 15628988968088756636647289)
  ·
    refine ⟨11721741726066567477485467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15628988968088756636647289 11721741726066567477485467)
    ·
      refine ⟨17582612589099851216228201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11721741726066567477485467 17582612589099851216228201)
      ·
        refine ⟨13186959441824888412171151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17582612589099851216228201 13186959441824888412171151)
        ·
          refine ⟨19780439162737332618256727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13186959441824888412171151 19780439162737332618256727)
          ·
            refine ⟨29670658744105998927385091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19780439162737332618256727 29670658744105998927385091)
            ·
              refine ⟨44505988116158998391077637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29670658744105998927385091 44505988116158998391077637)
              ·
                refine ⟨8344872771779812198327057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44505988116158998391077637 8344872771779812198327057)
                ·
                  refine ⟨6258654578834859148745293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344872771779812198327057 6258654578834859148745293)
                  ·
                    refine ⟨2346995467063072180779485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6258654578834859148745293 2346995467063072180779485)
                    ·
                      refine ⟨880123300148652067792307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2346995467063072180779485 880123300148652067792307)
                      ·
                        rfl

theorem cell23_1714034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1714034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714034 prefixEnd_1714034 := by exact prefixLift 1714034
  have htrace : WordTrace (prefixWord ++ tailWord_1714034) baseStart_1714034 baseEnd_1714034 := by
    simpa [prefixWord, tailWord_1714034, baseEnd_1714034] using wordTrace_append hprefix tailTrace_1714034
  have hstable : (prefixWord ++ tailWord_1714034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714034).length < 2 ^ (prefixWord ++ tailWord_1714034).sum := by decide
  have hdescent : baseEnd_1714034 < baseStart_1714034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714071 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 2, 5]
def baseStart_1714071 : Nat := 118140960795 + 1714071 * 2 ^ 59
def prefixEnd_1714071 : Nat := 4983230072969 + 3 ^ 40 * 1714071 * 2
def baseEnd_1714071 : Nat := 293380766310956141009879

theorem tailTrace_1714071 : CollatzResearch.WordTrace tailWord_1714071 prefixEnd_1714071 293380766310956141009879 := by
  unfold tailWord_1714071
  simp only [CollatzResearch.WordTrace]
  refine ⟨62517305373220981865686067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41678203582147321243790711 62517305373220981865686067)
  ·
    refine ⟨93775958059831472798529101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62517305373220981865686067 93775958059831472798529101)
    ·
      refine ⟨35165984272436802299448413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93775958059831472798529101 35165984272436802299448413)
      ·
        refine ⟨13187244102163800862293155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35165984272436802299448413 13187244102163800862293155)
        ·
          refine ⟨19780866153245701293439733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187244102163800862293155 19780866153245701293439733)
          ·
            refine ⟨1854456201866784496259975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19780866153245701293439733 1854456201866784496259975)
            ·
              refine ⟨2781684302800176744389963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854456201866784496259975 2781684302800176744389963)
              ·
                refine ⟨4172526454200265116584945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781684302800176744389963 4172526454200265116584945)
                ·
                  refine ⟨3129394840650198837438709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172526454200265116584945 3129394840650198837438709)
                  ·
                    refine ⟨293380766310956141009879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3129394840650198837438709 293380766310956141009879)
                    ·
                      rfl

theorem cell23_1714071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_1714071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714071 prefixEnd_1714071 := by exact prefixLift 1714071
  have htrace : WordTrace (prefixWord ++ tailWord_1714071) baseStart_1714071 baseEnd_1714071 := by
    simpa [prefixWord, tailWord_1714071, baseEnd_1714071] using wordTrace_append hprefix tailTrace_1714071
  have hstable : (prefixWord ++ tailWord_1714071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714071).length < 2 ^ (prefixWord ++ tailWord_1714071).sum := by decide
  have hdescent : baseEnd_1714071 < baseStart_1714071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714101 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_1714101 : Nat := 118140960795 + 1714101 * 2 ^ 59
def prefixEnd_1714101 : Nat := 4983230072969 + 3 ^ 40 * 1714101 * 2
def baseEnd_1714101 : Nat := 293385901117501101884833

theorem tailTrace_1714101 : CollatzResearch.WordTrace tailWord_1714101 prefixEnd_1714101 293385901117501101884833 := by
  unfold tailWord_1714101
  simp only [CollatzResearch.WordTrace]
  refine ⟨62518399563112296989278157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41678933042074864659518771 62518399563112296989278157)
  ·
    refine ⟨23444399836167111370979309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62518399563112296989278157 23444399836167111370979309)
    ·
      refine ⟨8791649938562666764117241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23444399836167111370979309 8791649938562666764117241)
      ·
        refine ⟨6593737453922000073087931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8791649938562666764117241 6593737453922000073087931)
        ·
          refine ⟨9890606180883000109631897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6593737453922000073087931 9890606180883000109631897)
          ·
            refine ⟨7417954635662250082223923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9890606180883000109631897 7417954635662250082223923)
            ·
              refine ⟨11126931953493375123335885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417954635662250082223923 11126931953493375123335885)
              ·
                refine ⟨4172599482560015671250957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11126931953493375123335885 4172599482560015671250957)
                ·
                  refine ⟨1564724805960005876719109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4172599482560015671250957 1564724805960005876719109)
                  ·
                    refine ⟨293385901117501101884833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1564724805960005876719109 293385901117501101884833)
                    ·
                      rfl

theorem cell23_1714101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_1714101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714101 prefixEnd_1714101 := by exact prefixLift 1714101
  have htrace : WordTrace (prefixWord ++ tailWord_1714101) baseStart_1714101 baseEnd_1714101 := by
    simpa [prefixWord, tailWord_1714101, baseEnd_1714101] using wordTrace_append hprefix tailTrace_1714101
  have hstable : (prefixWord ++ tailWord_1714101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714101).length < 2 ^ (prefixWord ++ tailWord_1714101).sum := by decide
  have hdescent : baseEnd_1714101 < baseStart_1714101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714181 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 4]
def baseStart_1714181 : Nat := 118140960795 + 1714181 * 2 ^ 59
def prefixEnd_1714181 : Nat := 4983230072969 + 3 ^ 40 * 1714181 * 2
def baseEnd_1714181 : Nat := 880198781804862992654131

theorem tailTrace_1714181 : CollatzResearch.WordTrace tailWord_1714181 prefixEnd_1714181 880198781804862992654131 := by
  unfold tailWord_1714181
  simp only [CollatzResearch.WordTrace]
  refine ⟨62521317402822470652190397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41680878268548313768126931 62521317402822470652190397)
  ·
    refine ⟨23445494026058426494571399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62521317402822470652190397 23445494026058426494571399)
    ·
      refine ⟨35168241039087639741857099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23445494026058426494571399 35168241039087639741857099)
      ·
        refine ⟨52752361558631459612785649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35168241039087639741857099 52752361558631459612785649)
        ·
          refine ⟨39564271168973594709589237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52752361558631459612785649 39564271168973594709589237)
          ·
            refine ⟨3709150422091274504023991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39564271168973594709589237 3709150422091274504023991)
            ·
              refine ⟨5563725633136911756035987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709150422091274504023991 5563725633136911756035987)
              ·
                refine ⟨8345588449705367634053981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563725633136911756035987 8345588449705367634053981)
                ·
                  refine ⟨3129595668639512862770243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8345588449705367634053981 3129595668639512862770243)
                  ·
                    refine ⟨4694393502959269294155365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3129595668639512862770243 4694393502959269294155365)
                    ·
                      refine ⟨880198781804862992654131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4694393502959269294155365 880198781804862992654131)
                      ·
                        rfl

theorem cell23_1714181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_1714181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714181 prefixEnd_1714181 := by exact prefixLift 1714181
  have htrace : WordTrace (prefixWord ++ tailWord_1714181) baseStart_1714181 baseEnd_1714181 := by
    simpa [prefixWord, tailWord_1714181, baseEnd_1714181] using wordTrace_append hprefix tailTrace_1714181
  have hstable : (prefixWord ++ tailWord_1714181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714181).length < 2 ^ (prefixWord ++ tailWord_1714181).sum := by decide
  have hdescent : baseEnd_1714181 < baseStart_1714181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714204 : List Nat := [2, 2, 3, 1, 3, 12]
def baseStart_1714204 : Nat := 118140960795 + 1714204 * 2 ^ 59
def prefixEnd_1714204 : Nat := 4983230072969 + 3 ^ 40 * 1714204 * 2
def baseEnd_1714204 : Nat := 3622265810123112768175

theorem tailTrace_1714204 : CollatzResearch.WordTrace tailWord_1714204 prefixEnd_1714204 3622265810123112768175 := by
  unfold tailWord_1714204
  simp only [CollatzResearch.WordTrace]
  refine ⟨31261078140869572790138833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41681437521159430386851777 31261078140869572790138833)
  ·
    refine ⟨23445808605652179592604125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31261078140869572790138833 23445808605652179592604125)
    ·
      refine ⟨8792178227119567347226547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23445808605652179592604125 8792178227119567347226547)
      ·
        refine ⟨13188267340679351020839821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792178227119567347226547 13188267340679351020839821)
        ·
          refine ⟨4945600252754756632814933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13188267340679351020839821 4945600252754756632814933)
          ·
            refine ⟨3622265810123112768175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4945600252754756632814933 3622265810123112768175)
            ·
              rfl

theorem cell23_1714204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 12].length) (baseStart_1714204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714204 prefixEnd_1714204 := by exact prefixLift 1714204
  have htrace : WordTrace (prefixWord ++ tailWord_1714204) baseStart_1714204 baseEnd_1714204 := by
    simpa [prefixWord, tailWord_1714204, baseEnd_1714204] using wordTrace_append hprefix tailTrace_1714204
  have hstable : (prefixWord ++ tailWord_1714204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714204).length < 2 ^ (prefixWord ++ tailWord_1714204).sum := by decide
  have hdescent : baseEnd_1714204 < baseStart_1714204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714209 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1714209 : Nat := 118140960795 + 1714209 * 2 ^ 59
def prefixEnd_1714209 : Nat := 4983230072969 + 3 ^ 40 * 1714209 * 2
def baseEnd_1714209 : Nat := 880213159263188883104003

theorem tailTrace_1714209 : CollatzResearch.WordTrace tailWord_1714209 prefixEnd_1714209 880213159263188883104003 := by
  unfold tailWord_1714209
  simp only [CollatzResearch.WordTrace]
  refine ⟨62522338646721031434209681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41681559097814020956139787 62522338646721031434209681)
  ·
    refine ⟨46891753985040773575657261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62522338646721031434209681 46891753985040773575657261)
    ·
      refine ⟨17584407744390290090871473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46891753985040773575657261 17584407744390290090871473)
      ·
        refine ⟨13188305808292717568153605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17584407744390290090871473 13188305808292717568153605)
        ·
          refine ⟨2472807339054884544028801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13188305808292717568153605 2472807339054884544028801)
          ·
            refine ⟨1854605504291163408021601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472807339054884544028801 1854605504291163408021601)
            ·
              refine ⟨1390954128218372556016201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854605504291163408021601 1390954128218372556016201)
              ·
                refine ⟨1043215596163779417012151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390954128218372556016201 1043215596163779417012151)
                ·
                  refine ⟨1564823394245669125518227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043215596163779417012151 1564823394245669125518227)
                  ·
                    refine ⟨2347235091368503688277341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1564823394245669125518227 2347235091368503688277341)
                    ·
                      refine ⟨880213159263188883104003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347235091368503688277341 880213159263188883104003)
                      ·
                        rfl

theorem cell23_1714209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1714209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714209 prefixEnd_1714209 := by exact prefixLift 1714209
  have htrace : WordTrace (prefixWord ++ tailWord_1714209) baseStart_1714209 baseEnd_1714209 := by
    simpa [prefixWord, tailWord_1714209, baseEnd_1714209] using wordTrace_append hprefix tailTrace_1714209
  have hstable : (prefixWord ++ tailWord_1714209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714209).length < 2 ^ (prefixWord ++ tailWord_1714209).sum := by decide
  have hdescent : baseEnd_1714209 < baseStart_1714209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714218 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3]
def baseStart_1714218 : Nat := 118140960795 + 1714218 * 2 ^ 59
def prefixEnd_1714218 : Nat := 4983230072969 + 3 ^ 40 * 1714218 * 2
def baseEnd_1714218 : Nat := 880217780589079347891461

theorem tailTrace_1714218 : CollatzResearch.WordTrace tailWord_1714218 prefixEnd_1714218 880217780589079347891461 := by
  unfold tailWord_1714218
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630666725922106492821827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41681777935792283980858205 15630666725922106492821827)
  ·
    refine ⟨23446000088883159739232741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630666725922106492821827 23446000088883159739232741)
    ·
      refine ⟨4396125016665592451106139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23446000088883159739232741 4396125016665592451106139)
      ·
        refine ⟨6594187524998388676659209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396125016665592451106139 6594187524998388676659209)
        ·
          refine ⟨4945640643748791507494407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594187524998388676659209 4945640643748791507494407)
          ·
            refine ⟨7418460965623187261241611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945640643748791507494407 7418460965623187261241611)
            ·
              refine ⟨11127691448434780891862417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7418460965623187261241611 11127691448434780891862417)
              ·
                refine ⟨8345768586326085668896813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11127691448434780891862417 8345768586326085668896813)
                ·
                  refine ⟨3129663219872282125836305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8345768586326085668896813 3129663219872282125836305)
                  ·
                    refine ⟨2347247414904211594377229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3129663219872282125836305 2347247414904211594377229)
                    ·
                      refine ⟨880217780589079347891461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347247414904211594377229 880217780589079347891461)
                      ·
                        rfl

theorem cell23_1714218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_1714218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714218 prefixEnd_1714218 := by exact prefixLift 1714218
  have htrace : WordTrace (prefixWord ++ tailWord_1714218) baseStart_1714218 baseEnd_1714218 := by
    simpa [prefixWord, tailWord_1714218, baseEnd_1714218] using wordTrace_append hprefix tailTrace_1714218
  have hstable : (prefixWord ++ tailWord_1714218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714218).length < 2 ^ (prefixWord ++ tailWord_1714218).sum := by decide
  have hdescent : baseEnd_1714218 < baseStart_1714218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714231 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3]
def baseStart_1714231 : Nat := 118140960795 + 1714231 * 2 ^ 59
def prefixEnd_1714231 : Nat := 4983230072969 + 3 ^ 40 * 1714231 * 2
def baseEnd_1714231 : Nat := 880224455837587797028901

theorem tailTrace_1714231 : CollatzResearch.WordTrace tailWord_1714231 prefixEnd_1714231 880224455837587797028901 := by
  unfold tailWord_1714231
  simp only [CollatzResearch.WordTrace]
  refine ⟨62523141052641329191510547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41682094035094219461007031 62523141052641329191510547)
  ·
    refine ⟨93784711578961993787265821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62523141052641329191510547 93784711578961993787265821)
    ·
      refine ⟨35169266842110747670224683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93784711578961993787265821 35169266842110747670224683)
      ·
        refine ⟨52753900263166121505337025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35169266842110747670224683 52753900263166121505337025)
        ·
          refine ⟨39565425197374591129002769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52753900263166121505337025 39565425197374591129002769)
          ·
            refine ⟨29674068898030943346752077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39565425197374591129002769 29674068898030943346752077)
            ·
              refine ⟨11127775836761603755032029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29674068898030943346752077 11127775836761603755032029)
              ·
                refine ⟨4172915938785601408137011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11127775836761603755032029 4172915938785601408137011)
                ·
                  refine ⟨6259373908178402112205517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4172915938785601408137011 6259373908178402112205517)
                  ·
                    refine ⟨2347265215566900792077069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6259373908178402112205517 2347265215566900792077069)
                    ·
                      refine ⟨880224455837587797028901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347265215566900792077069 880224455837587797028901)
                      ·
                        rfl

theorem cell23_1714231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 3, 3].length) (baseStart_1714231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714231 prefixEnd_1714231 := by exact prefixLift 1714231
  have htrace : WordTrace (prefixWord ++ tailWord_1714231) baseStart_1714231 baseEnd_1714231 := by
    simpa [prefixWord, tailWord_1714231, baseEnd_1714231] using wordTrace_append hprefix tailTrace_1714231
  have hstable : (prefixWord ++ tailWord_1714231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714231).length < 2 ^ (prefixWord ++ tailWord_1714231).sum := by decide
  have hdescent : baseEnd_1714231 < baseStart_1714231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714234 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 7]
def baseStart_1714234 : Nat := 118140960795 + 1714234 * 2 ^ 59
def prefixEnd_1714234 : Nat := 4983230072969 + 3 ^ 40 * 1714234 * 2
def baseEnd_1714234 : Nat := 293408665426517095097129

theorem tailTrace_1714234 : CollatzResearch.WordTrace tailWord_1714234 prefixEnd_1714234 293408665426517095097129 := by
  unfold tailWord_1714234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630812617907615175967439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41682166981086973802579837 15630812617907615175967439)
  ·
    refine ⟨23446218926861422763951159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15630812617907615175967439 23446218926861422763951159)
    ·
      refine ⟨35169328390292134145926739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23446218926861422763951159 35169328390292134145926739)
      ·
        refine ⟨52753992585438201218890109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35169328390292134145926739 52753992585438201218890109)
        ·
          refine ⟨19782747219539325457083791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52753992585438201218890109 19782747219539325457083791)
          ·
            refine ⟨29674120829308988185625687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782747219539325457083791 29674120829308988185625687)
            ·
              refine ⟨44511181243963482278438531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29674120829308988185625687 44511181243963482278438531)
              ·
                refine ⟨66766771865945223417657797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44511181243963482278438531 66766771865945223417657797)
                ·
                  refine ⟨12518769724864729390810837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66766771865945223417657797 12518769724864729390810837)
                  ·
                    refine ⟨293408665426517095097129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12518769724864729390810837 293408665426517095097129)
                    ·
                      rfl

theorem cell23_1714234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 7].length) (baseStart_1714234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714234 prefixEnd_1714234 := by exact prefixLift 1714234
  have htrace : WordTrace (prefixWord ++ tailWord_1714234) baseStart_1714234 baseEnd_1714234 := by
    simpa [prefixWord, tailWord_1714234, baseEnd_1714234] using wordTrace_append hprefix tailTrace_1714234
  have hstable : (prefixWord ++ tailWord_1714234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714234).length < 2 ^ (prefixWord ++ tailWord_1714234).sum := by decide
  have hdescent : baseEnd_1714234 < baseStart_1714234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714282 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3]
def baseStart_1714282 : Nat := 118140960795 + 1714282 * 2 ^ 59
def prefixEnd_1714282 : Nat := 4983230072969 + 3 ^ 40 * 1714282 * 2
def baseEnd_1714282 : Nat := 880250643350967097491167

theorem tailTrace_1714282 : CollatzResearch.WordTrace tailWord_1714282 prefixEnd_1714282 880250643350967097491167 := by
  unfold tailWord_1714282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631250293864141225404275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41683334116971043267744733 15631250293864141225404275)
  ·
    refine ⟨23446875440796211838106413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15631250293864141225404275 23446875440796211838106413)
    ·
      refine ⟨8792578290298579439289905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23446875440796211838106413 8792578290298579439289905)
      ·
        refine ⟨6594433717723934579467429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8792578290298579439289905 6594433717723934579467429)
        ·
          refine ⟨1236456322073237733650143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6594433717723934579467429 1236456322073237733650143)
          ·
            refine ⟨1854684483109856600475215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236456322073237733650143 1854684483109856600475215)
            ·
              refine ⟨2782026724664784900712823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854684483109856600475215 2782026724664784900712823)
              ·
                refine ⟨4173040086997177351069235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782026724664784900712823 4173040086997177351069235)
                ·
                  refine ⟨6259560130495766026603853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173040086997177351069235 6259560130495766026603853)
                  ·
                    refine ⟨2347335048935912259976445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6259560130495766026603853 2347335048935912259976445)
                    ·
                      refine ⟨880250643350967097491167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347335048935912259976445 880250643350967097491167)
                      ·
                        rfl

theorem cell23_1714282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_1714282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714282 prefixEnd_1714282 := by exact prefixLift 1714282
  have htrace : WordTrace (prefixWord ++ tailWord_1714282) baseStart_1714282 baseEnd_1714282 := by
    simpa [prefixWord, tailWord_1714282, baseEnd_1714282] using wordTrace_append hprefix tailTrace_1714282
  have hstable : (prefixWord ++ tailWord_1714282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714282).length < 2 ^ (prefixWord ++ tailWord_1714282).sum := by decide
  have hdescent : baseEnd_1714282 < baseStart_1714282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714322 : List Nat := [3, 2, 3, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_1714322 : Nat := 118140960795 + 1714322 * 2 ^ 59
def prefixEnd_1714322 : Nat := 4983230072969 + 3 ^ 40 * 1714322 * 2
def baseEnd_1714322 : Nat := 880271182577146940990983

theorem tailTrace_1714322 : CollatzResearch.WordTrace tailWord_1714322 prefixEnd_1714322 880271182577146940990983 := by
  unfold tailWord_1714322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15631615023827912933268305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41684306730207767822048813 15631615023827912933268305)
  ·
    refine ⟨11723711267870934699951229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15631615023827912933268305 11723711267870934699951229)
    ·
      refine ⟨4396391725451600512481711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11723711267870934699951229 4396391725451600512481711)
      ·
        refine ⟨6594587588177400768722567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396391725451600512481711 6594587588177400768722567)
        ·
          refine ⟨9891881382266101153083851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6594587588177400768722567 9891881382266101153083851)
          ·
            refine ⟨14837822073399151729625777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9891881382266101153083851 14837822073399151729625777)
            ·
              refine ⟨11128366555049363797219333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14837822073399151729625777 11128366555049363797219333)
              ·
                refine ⟨2086568729071755711978625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11128366555049363797219333 2086568729071755711978625)
                ·
                  refine ⟨1564926546803816783983969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086568729071755711978625 1564926546803816783983969)
                  ·
                    refine ⟨1173694910102862587987977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1564926546803816783983969 1173694910102862587987977)
                    ·
                      refine ⟨880271182577146940990983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173694910102862587987977 880271182577146940990983)
                      ·
                        rfl

theorem cell23_1714322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_1714322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714322 prefixEnd_1714322 := by exact prefixLift 1714322
  have htrace : WordTrace (prefixWord ++ tailWord_1714322) baseStart_1714322 baseEnd_1714322 := by
    simpa [prefixWord, tailWord_1714322, baseEnd_1714322] using wordTrace_append hprefix tailTrace_1714322
  have hstable : (prefixWord ++ tailWord_1714322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714322).length < 2 ^ (prefixWord ++ tailWord_1714322).sum := by decide
  have hdescent : baseEnd_1714322 < baseStart_1714322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714341 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_1714341 : Nat := 118140960795 + 1714341 * 2 ^ 59
def prefixEnd_1714341 : Nat := 4983230072969 + 3 ^ 40 * 1714341 * 2
def baseEnd_1714341 : Nat := 293426979569860788884465

theorem tailTrace_1714341 : CollatzResearch.WordTrace tailWord_1714341 prefixEnd_1714341 293426979569860788884465 := by
  unfold tailWord_1714341
  simp only [CollatzResearch.WordTrace]
  refine ⟨62527153082242817978014877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41684768721495211985343251 62527153082242817978014877)
  ·
    refine ⟨23447682405841056741755579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62527153082242817978014877 23447682405841056741755579)
    ·
      refine ⟨35171523608761585112633369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23447682405841056741755579 35171523608761585112633369)
      ·
        refine ⟨26378642706571188834475027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35171523608761585112633369 26378642706571188834475027)
        ·
          refine ⟨39567964059856783251712541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26378642706571188834475027 39567964059856783251712541)
          ·
            refine ⟨14837986522446293719392203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39567964059856783251712541 14837986522446293719392203)
            ·
              refine ⟨22256979783669440579088305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14837986522446293719392203 22256979783669440579088305)
              ·
                refine ⟨16692734837752080434316229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22256979783669440579088305 16692734837752080434316229)
                ·
                  refine ⟨3129887782078515081434293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16692734837752080434316229 3129887782078515081434293)
                  ·
                    refine ⟨293426979569860788884465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3129887782078515081434293 293426979569860788884465)
                    ·
                      rfl

theorem cell23_1714341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_1714341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714341 prefixEnd_1714341 := by exact prefixLift 1714341
  have htrace : WordTrace (prefixWord ++ tailWord_1714341) baseStart_1714341 baseEnd_1714341 := by
    simpa [prefixWord, tailWord_1714341, baseEnd_1714341] using wordTrace_append hprefix tailTrace_1714341
  have hstable : (prefixWord ++ tailWord_1714341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714341).length < 2 ^ (prefixWord ++ tailWord_1714341).sum := by decide
  have hdescent : baseEnd_1714341 < baseStart_1714341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714356 : List Nat := [2, 5, 3, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1714356 : Nat := 118140960795 + 1714356 * 2 ^ 59
def prefixEnd_1714356 : Nat := 4983230072969 + 3 ^ 40 * 1714356 * 2
def baseEnd_1714356 : Nat := 880288640919399807965827

theorem tailTrace_1714356 : CollatzResearch.WordTrace tailWord_1714356 prefixEnd_1714356 880288640919399807965827 := by
  unfold tailWord_1714356
  simp only [CollatzResearch.WordTrace]
  refine ⟨31263850088594237769905461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41685133451458983693207281 31263850088594237769905461)
  ·
    refine ⟨2930985945805709790928637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31263850088594237769905461 2930985945805709790928637)
    ·
      refine ⟨1099119729677141171598239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2930985945805709790928637 1099119729677141171598239)
      ·
        refine ⟨1648679594515711757397359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099119729677141171598239 1648679594515711757397359)
        ·
          refine ⟨2473019391773567636096039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648679594515711757397359 2473019391773567636096039)
          ·
            refine ⟨3709529087660351454144059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473019391773567636096039 3709529087660351454144059)
            ·
              refine ⟨5564293631490527181216089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709529087660351454144059 5564293631490527181216089)
              ·
                refine ⟨4173220223617895385912067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564293631490527181216089 4173220223617895385912067)
                ·
                  refine ⟨6259830335426843078868101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173220223617895385912067 6259830335426843078868101)
                  ·
                    refine ⟨1173718187892533077287769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6259830335426843078868101 1173718187892533077287769)
                    ·
                      refine ⟨880288640919399807965827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173718187892533077287769 880288640919399807965827)
                      ·
                        rfl

theorem cell23_1714356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1714356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714356 prefixEnd_1714356 := by exact prefixLift 1714356
  have htrace : WordTrace (prefixWord ++ tailWord_1714356) baseStart_1714356 baseEnd_1714356 := by
    simpa [prefixWord, tailWord_1714356, baseEnd_1714356] using wordTrace_append hprefix tailTrace_1714356
  have hstable : (prefixWord ++ tailWord_1714356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714356).length < 2 ^ (prefixWord ++ tailWord_1714356).sum := by decide
  have hdescent : baseEnd_1714356 < baseStart_1714356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714378 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4]
def baseStart_1714378 : Nat := 118140960795 + 1714378 * 2 ^ 59
def prefixEnd_1714378 : Nat := 4983230072969 + 3 ^ 40 * 1714378 * 2
def baseEnd_1714378 : Nat := 880299937493798721890725

theorem tailTrace_1714378 : CollatzResearch.WordTrace tailWord_1714378 prefixEnd_1714378 880299937493798721890725 := by
  unfold tailWord_1714378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632125645777193324277947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41685668388739182198074525 15632125645777193324277947)
  ·
    refine ⟨23448188468665789986416921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15632125645777193324277947 23448188468665789986416921)
    ·
      refine ⟨17586141351499342489812691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23448188468665789986416921 17586141351499342489812691)
      ·
        refine ⟨26379212027249013734719037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17586141351499342489812691 26379212027249013734719037)
        ·
          refine ⟨9892204510218380150519639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26379212027249013734719037 9892204510218380150519639)
          ·
            refine ⟨14838306765327570225779459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892204510218380150519639 14838306765327570225779459)
            ·
              refine ⟨22257460147991355338669189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838306765327570225779459 22257460147991355338669189)
              ·
                refine ⟨4173273777748379126000473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22257460147991355338669189 4173273777748379126000473)
                ·
                  refine ⟨3129955333311284344500355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173273777748379126000473 3129955333311284344500355)
                  ·
                    refine ⟨4694932999966926516750533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3129955333311284344500355 4694932999966926516750533)
                    ·
                      refine ⟨880299937493798721890725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4694932999966926516750533 880299937493798721890725)
                      ·
                        rfl

theorem cell23_1714378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_1714378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714378 prefixEnd_1714378 := by exact prefixLift 1714378
  have htrace : WordTrace (prefixWord ++ tailWord_1714378) baseStart_1714378 baseEnd_1714378 := by
    simpa [prefixWord, tailWord_1714378, baseEnd_1714378] using wordTrace_append hprefix tailTrace_1714378
  have hstable : (prefixWord ++ tailWord_1714378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714378).length < 2 ^ (prefixWord ++ tailWord_1714378).sum := by decide
  have hdescent : baseEnd_1714378 < baseStart_1714378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714391 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1714391 : Nat := 118140960795 + 1714391 * 2 ^ 59
def prefixEnd_1714391 : Nat := 4983230072969 + 3 ^ 40 * 1714391 * 2
def baseEnd_1714391 : Nat := 880306612742307171028165

theorem tailTrace_1714391 : CollatzResearch.WordTrace tailWord_1714391 prefixEnd_1714391 880306612742307171028165 := by
  unfold tailWord_1714391
  simp only [CollatzResearch.WordTrace]
  refine ⟨62528976732061676517335027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41685984488041117678223351 62528976732061676517335027)
  ·
    refine ⟨93793465098092514776002541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62528976732061676517335027 93793465098092514776002541)
    ·
      refine ⟨35172549411784693041000953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93793465098092514776002541 35172549411784693041000953)
      ·
        refine ⟨26379412058838519780750715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35172549411784693041000953 26379412058838519780750715)
        ·
          refine ⟨39569118088257779671126073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26379412058838519780750715 39569118088257779671126073)
          ·
            refine ⟨29676838566193334753344555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39569118088257779671126073 29676838566193334753344555)
            ·
              refine ⟨44515257849290002130016833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29676838566193334753344555 44515257849290002130016833)
              ·
                refine ⟨33386443386967501597512625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44515257849290002130016833 33386443386967501597512625)
                ·
                  refine ⟨25039832540225626198134469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33386443386967501597512625 25039832540225626198134469)
                  ·
                    refine ⟨4694968601292304912150213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25039832540225626198134469 4694968601292304912150213)
                    ·
                      refine ⟨880306612742307171028165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4694968601292304912150213 880306612742307171028165)
                      ·
                        rfl

theorem cell23_1714391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1714391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714391 prefixEnd_1714391 := by exact prefixLift 1714391
  have htrace : WordTrace (prefixWord ++ tailWord_1714391) baseStart_1714391 baseEnd_1714391 := by
    simpa [prefixWord, tailWord_1714391, baseEnd_1714391] using wordTrace_append hprefix tailTrace_1714391
  have hstable : (prefixWord ++ tailWord_1714391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714391).length < 2 ^ (prefixWord ++ tailWord_1714391).sum := by decide
  have hdescent : baseEnd_1714391 < baseStart_1714391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714405 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 3, 4]
def baseStart_1714405 : Nat := 118140960795 + 1714405 * 2 ^ 59
def prefixEnd_1714405 : Nat := 4983230072969 + 3 ^ 40 * 1714405 * 2
def baseEnd_1714405 : Nat := 293437933823823372084367

theorem tailTrace_1714405 : CollatzResearch.WordTrace tailWord_1714405 prefixEnd_1714405 293437933823823372084367 := by
  unfold tailWord_1714405
  simp only [CollatzResearch.WordTrace]
  refine ⟨62529487354010956908344669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41686324902673971272229779 62529487354010956908344669)
  ·
    refine ⟨23448557757754108840629251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62529487354010956908344669 23448557757754108840629251)
    ·
      refine ⟨35172836636631163260943877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23448557757754108840629251 35172836636631163260943877)
      ·
        refine ⟨6594906869368343111426977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35172836636631163260943877 6594906869368343111426977)
        ·
          refine ⟨4946180152026257333570233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594906869368343111426977 4946180152026257333570233)
          ·
            refine ⟨3709635114019693000177675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4946180152026257333570233 3709635114019693000177675)
            ·
              refine ⟨5564452671029539500266513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709635114019693000177675 5564452671029539500266513)
              ·
                refine ⟨4173339503272154625199885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5564452671029539500266513 4173339503272154625199885)
                ·
                  refine ⟨1565002313727057984449957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4173339503272154625199885 1565002313727057984449957)
                  ·
                    refine ⟨293437933823823372084367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565002313727057984449957 293437933823823372084367)
                    ·
                      rfl

theorem cell23_1714405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 4].length) (baseStart_1714405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714405 prefixEnd_1714405 := by exact prefixLift 1714405
  have htrace : WordTrace (prefixWord ++ tailWord_1714405) baseStart_1714405 baseEnd_1714405 := by
    simpa [prefixWord, tailWord_1714405, baseEnd_1714405] using wordTrace_append hprefix tailTrace_1714405
  have hstable : (prefixWord ++ tailWord_1714405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714405).length < 2 ^ (prefixWord ++ tailWord_1714405).sum := by decide
  have hdescent : baseEnd_1714405 < baseStart_1714405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714415 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3]
def baseStart_1714415 : Nat := 118140960795 + 1714415 * 2 ^ 59
def prefixEnd_1714415 : Nat := 4983230072969 + 3 ^ 40 * 1714415 * 2
def baseEnd_1714415 : Nat := 880318936278015077128055

theorem tailTrace_1714415 : CollatzResearch.WordTrace tailWord_1714415 prefixEnd_1714415 880318936278015077128055 := by
  unfold tailWord_1714415
  simp only [CollatzResearch.WordTrace]
  refine ⟨62529852083974728616208699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41686568055983152410805799 62529852083974728616208699)
  ·
    refine ⟨93794778125962092924313049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62529852083974728616208699 93794778125962092924313049)
    ·
      refine ⟨70346083594471569693234787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93794778125962092924313049 70346083594471569693234787)
      ·
        refine ⟨105519125391707354539852181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70346083594471569693234787 105519125391707354539852181)
        ·
          refine ⟨4946209002736282244055571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105519125391707354539852181 4946209002736282244055571)
          ·
            refine ⟨7419313504104423366083357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946209002736282244055571 7419313504104423366083357)
            ·
              refine ⟨2782242564039158762281259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7419313504104423366083357 2782242564039158762281259)
              ·
                refine ⟨4173363846058738143421889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782242564039158762281259 4173363846058738143421889)
                ·
                  refine ⟨3130022884544053607566417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173363846058738143421889 3130022884544053607566417)
                  ·
                    refine ⟨2347517163408040205674813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3130022884544053607566417 2347517163408040205674813)
                    ·
                      refine ⟨880318936278015077128055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347517163408040205674813 880318936278015077128055)
                      ·
                        rfl

theorem cell23_1714415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 3].length) (baseStart_1714415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714415 prefixEnd_1714415 := by exact prefixLift 1714415
  have htrace : WordTrace (prefixWord ++ tailWord_1714415) baseStart_1714415 baseEnd_1714415 := by
    simpa [prefixWord, tailWord_1714415, baseEnd_1714415] using wordTrace_append hprefix tailTrace_1714415
  have hstable : (prefixWord ++ tailWord_1714415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714415).length < 2 ^ (prefixWord ++ tailWord_1714415).sum := by decide
  have hdescent : baseEnd_1714415 < baseStart_1714415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714422 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1714422 : Nat := 118140960795 + 1714422 * 2 ^ 59
def prefixEnd_1714422 : Nat := 4983230072969 + 3 ^ 40 * 1714422 * 2
def baseEnd_1714422 : Nat := 293440843547532183246841

theorem tailTrace_1714422 : CollatzResearch.WordTrace tailWord_1714422 prefixEnd_1714422 293440843547532183246841 := by
  unfold tailWord_1714422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908131712184335550732095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41686738263299579207809013 3908131712184335550732095)
  ·
    refine ⟨5862197568276503326098143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3908131712184335550732095 5862197568276503326098143)
    ·
      refine ⟨8793296352414754989147215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5862197568276503326098143 8793296352414754989147215)
      ·
        refine ⟨13189944528622132483720823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8793296352414754989147215 13189944528622132483720823)
        ·
          refine ⟨19784916792933198725581235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189944528622132483720823 19784916792933198725581235)
          ·
            refine ⟨29677375189399798088371853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19784916792933198725581235 29677375189399798088371853)
            ·
              refine ⟨11129015696024924283139445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29677375189399798088371853 11129015696024924283139445)
              ·
                refine ⟨1043345221502336651544323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11129015696024924283139445 1043345221502336651544323)
                ·
                  refine ⟨1565017832253504977316485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043345221502336651544323 1565017832253504977316485)
                  ·
                    refine ⟨293440843547532183246841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565017832253504977316485 293440843547532183246841)
                    ·
                      rfl

theorem cell23_1714422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1714422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714422 prefixEnd_1714422 := by exact prefixLift 1714422
  have htrace : WordTrace (prefixWord ++ tailWord_1714422) baseStart_1714422 baseEnd_1714422 := by
    simpa [prefixWord, tailWord_1714422, baseEnd_1714422] using wordTrace_append hprefix tailTrace_1714422
  have hstable : (prefixWord ++ tailWord_1714422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714422).length < 2 ^ (prefixWord ++ tailWord_1714422).sum := by decide
  have hdescent : baseEnd_1714422 < baseStart_1714422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714455 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 1, 5, 2]
def baseStart_1714455 : Nat := 118140960795 + 1714455 * 2 ^ 59
def prefixEnd_1714455 : Nat := 4983230072969 + 3 ^ 40 * 1714455 * 2
def baseEnd_1714455 : Nat := 880339475504194920627871

theorem tailTrace_1714455 : CollatzResearch.WordTrace tailWord_1714455 prefixEnd_1714455 880339475504194920627871 := by
  unfold tailWord_1714455
  simp only [CollatzResearch.WordTrace]
  refine ⟨62531311003829815447664819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41687540669219876965109879 62531311003829815447664819)
  ·
    refine ⟨93796966505744723171497229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62531311003829815447664819 93796966505744723171497229)
    ·
      refine ⟨35173862439654271189311461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93796966505744723171497229 35173862439654271189311461)
      ·
        refine ⟨6595099207435175847995899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35173862439654271189311461 6595099207435175847995899)
        ·
          refine ⟨9892648811152763771993849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595099207435175847995899 9892648811152763771993849)
          ·
            refine ⟨7419486608364572828995387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9892648811152763771993849 7419486608364572828995387)
            ·
              refine ⟨11129229912546859243493081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419486608364572828995387 11129229912546859243493081)
              ·
                refine ⟨8346922434410144432619811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11129229912546859243493081 8346922434410144432619811)
                ·
                  refine ⟨12520383651615216648929717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8346922434410144432619811 12520383651615216648929717)
                  ·
                    refine ⟨1173785967338926560837161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12520383651615216648929717 1173785967338926560837161)
                    ·
                      refine ⟨880339475504194920627871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173785967338926560837161 880339475504194920627871)
                      ·
                        rfl

theorem cell23_1714455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_1714455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714455 prefixEnd_1714455 := by exact prefixLift 1714455
  have htrace : WordTrace (prefixWord ++ tailWord_1714455) baseStart_1714455 baseEnd_1714455 := by
    simpa [prefixWord, tailWord_1714455, baseEnd_1714455] using wordTrace_append hprefix tailTrace_1714455
  have hstable : (prefixWord ++ tailWord_1714455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714455).length < 2 ^ (prefixWord ++ tailWord_1714455).sum := by decide
  have hdescent : baseEnd_1714455 < baseStart_1714455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714485 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_1714485 : Nat := 118140960795 + 1714485 * 2 ^ 59
def prefixEnd_1714485 : Nat := 4983230072969 + 3 ^ 40 * 1714485 * 2
def baseEnd_1714485 : Nat := 880354879923829803252733

theorem tailTrace_1714485 : CollatzResearch.WordTrace tailWord_1714485 prefixEnd_1714485 880354879923829803252733 := by
  unfold tailWord_1714485
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532405193721130571256909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41688270129147420380837939 62532405193721130571256909)
  ·
    refine ⟨23449651947645423964221341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62532405193721130571256909 23449651947645423964221341)
    ·
      refine ⟨8793619480367033986583003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23449651947645423964221341 8793619480367033986583003)
      ·
        refine ⟨13190429220550550979874505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8793619480367033986583003 13190429220550550979874505)
        ·
          refine ⟨9892821915412913234905879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13190429220550550979874505 9892821915412913234905879)
          ·
            refine ⟨14839232873119369852358819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892821915412913234905879 14839232873119369852358819)
            ·
              refine ⟨22258849309679054778538229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14839232873119369852358819 22258849309679054778538229)
              ·
                refine ⟨2086767122782411385487959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22258849309679054778538229 2086767122782411385487959)
                ·
                  refine ⟨3130150684173617078231939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086767122782411385487959 3130150684173617078231939)
                  ·
                    refine ⟨4695226026260425617347909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3130150684173617078231939 4695226026260425617347909)
                    ·
                      refine ⟨880354879923829803252733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4695226026260425617347909 880354879923829803252733)
                      ·
                        rfl

theorem cell23_1714485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_1714485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714485 prefixEnd_1714485 := by exact prefixLift 1714485
  have htrace : WordTrace (prefixWord ++ tailWord_1714485) baseStart_1714485 baseEnd_1714485 := by
    simpa [prefixWord, tailWord_1714485, baseEnd_1714485] using wordTrace_append hprefix tailTrace_1714485
  have hstable : (prefixWord ++ tailWord_1714485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714485).length < 2 ^ (prefixWord ++ tailWord_1714485).sum := by decide
  have hdescent : baseEnd_1714485 < baseStart_1714485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714488 : List Nat := [2, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_1714488 : Nat := 118140960795 + 1714488 * 2 ^ 59
def prefixEnd_1714488 : Nat := 4983230072969 + 3 ^ 40 * 1714488 * 2
def baseEnd_1714488 : Nat := 880356420365793291515219

theorem tailTrace_1714488 : CollatzResearch.WordTrace tailWord_1714488 prefixEnd_1714488 880356420365793291515219 := by
  unfold tailWord_1714488
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266257306355131041808059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41688343075140174722410745 31266257306355131041808059)
  ·
    refine ⟨46899385959532696562712089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31266257306355131041808059 46899385959532696562712089)
    ·
      refine ⟨35174539469649522422034067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46899385959532696562712089 35174539469649522422034067)
      ·
        refine ⟨52761809204474283633051101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35174539469649522422034067 52761809204474283633051101)
        ·
          refine ⟨19785678451677856362394163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52761809204474283633051101 19785678451677856362394163)
          ·
            refine ⟨29678517677516784543591245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19785678451677856362394163 29678517677516784543591245)
            ·
              refine ⟨11129444129068794203846717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29678517677516784543591245 11129444129068794203846717)
              ·
                refine ⟨4173541548400797826442519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11129444129068794203846717 4173541548400797826442519)
                ·
                  refine ⟨6260312322601196739663779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173541548400797826442519 6260312322601196739663779)
                  ·
                    refine ⟨9390468483901795109495669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6260312322601196739663779 9390468483901795109495669)
                    ·
                      refine ⟨880356420365793291515219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9390468483901795109495669 880356420365793291515219)
                      ·
                        rfl

theorem cell23_1714488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_1714488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714488 prefixEnd_1714488 := by exact prefixLift 1714488
  have htrace : WordTrace (prefixWord ++ tailWord_1714488) baseStart_1714488 baseEnd_1714488 := by
    simpa [prefixWord, tailWord_1714488, baseEnd_1714488] using wordTrace_append hprefix tailTrace_1714488
  have hstable : (prefixWord ++ tailWord_1714488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714488).length < 2 ^ (prefixWord ++ tailWord_1714488).sum := by decide
  have hdescent : baseEnd_1714488 < baseStart_1714488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714495 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 2, 4]
def baseStart_1714495 : Nat := 118140960795 + 1714495 * 2 ^ 59
def prefixEnd_1714495 : Nat := 4983230072969 + 3 ^ 40 * 1714495 * 2
def baseEnd_1714495 : Nat := 293453338243458254709229

theorem tailTrace_1714495 : CollatzResearch.WordTrace tailWord_1714495 prefixEnd_1714495 293453338243458254709229 := by
  unfold tailWord_1714495
  simp only [CollatzResearch.WordTrace]
  refine ⟨62532769923684902279120939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41688513282456601519413959 62532769923684902279120939)
  ·
    refine ⟨93799154885527353418681409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62532769923684902279120939 93799154885527353418681409)
    ·
      refine ⟨70349366164145515064011057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93799154885527353418681409 70349366164145515064011057)
      ·
        refine ⟨52762024623109136298008293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70349366164145515064011057 52762024623109136298008293)
        ·
          refine ⟨9892879616832963055876555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52762024623109136298008293 9892879616832963055876555)
          ·
            refine ⟨14839319425249444583814833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892879616832963055876555 14839319425249444583814833)
            ·
              refine ⟨11129489568937083437861125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14839319425249444583814833 11129489568937083437861125)
              ·
                refine ⟨2086779294175703144598961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11129489568937083437861125 2086779294175703144598961)
                ·
                  refine ⟨1565084470631777358449221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086779294175703144598961 1565084470631777358449221)
                  ·
                    refine ⟨293453338243458254709229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565084470631777358449221 293453338243458254709229)
                    ·
                      rfl

theorem cell23_1714495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 4].length) (baseStart_1714495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714495 prefixEnd_1714495 := by exact prefixLift 1714495
  have htrace : WordTrace (prefixWord ++ tailWord_1714495) baseStart_1714495 baseEnd_1714495 := by
    simpa [prefixWord, tailWord_1714495, baseEnd_1714495] using wordTrace_append hprefix tailTrace_1714495
  have hstable : (prefixWord ++ tailWord_1714495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714495).length < 2 ^ (prefixWord ++ tailWord_1714495).sum := by decide
  have hdescent : baseEnd_1714495 < baseStart_1714495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714508 : List Nat := [2, 2, 1, 3, 2, 1, 4, 8]
def baseStart_1714508 : Nat := 118140960795 + 1714508 * 2 ^ 59
def prefixEnd_1714508 : Nat := 4983230072969 + 3 ^ 40 * 1714508 * 2
def baseEnd_1714508 : Nat := 32606173702921600491301

theorem tailTrace_1714508 : CollatzResearch.WordTrace tailWord_1714508 prefixEnd_1714508 32606173702921600491301 := by
  unfold tailWord_1714508
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266622036318902749672089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41688829381758536999562785 31266622036318902749672089)
  ·
    refine ⟨23449966527239177062254067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31266622036318902749672089 23449966527239177062254067)
    ·
      refine ⟨35174949790858765593381101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23449966527239177062254067 35174949790858765593381101)
      ·
        refine ⟨13190606171572037097517913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35174949790858765593381101 13190606171572037097517913)
        ·
          refine ⟨9892954628679027823138435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13190606171572037097517913 9892954628679027823138435)
          ·
            refine ⟨14839431943018541734707653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892954628679027823138435 14839431943018541734707653)
            ·
              refine ⟨2782393489315976575257685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14839431943018541734707653 2782393489315976575257685)
              ·
                refine ⟨32606173702921600491301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2782393489315976575257685 32606173702921600491301)
                ·
                  rfl

theorem cell23_1714508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 8].length) (baseStart_1714508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714508 prefixEnd_1714508 := by exact prefixLift 1714508
  have htrace : WordTrace (prefixWord ++ tailWord_1714508) baseStart_1714508 baseEnd_1714508 := by
    simpa [prefixWord, tailWord_1714508, baseEnd_1714508] using wordTrace_append hprefix tailTrace_1714508
  have hstable : (prefixWord ++ tailWord_1714508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714508).length < 2 ^ (prefixWord ++ tailWord_1714508).sum := by decide
  have hdescent : baseEnd_1714508 < baseStart_1714508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714512 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 2, 4]
def baseStart_1714512 : Nat := 118140960795 + 1714512 * 2 ^ 59
def prefixEnd_1714512 : Nat := 4983230072969 + 3 ^ 40 * 1714512 * 2
def baseEnd_1714512 : Nat := 293456247967167065871703

theorem tailTrace_1714512 : CollatzResearch.WordTrace tailWord_1714512 prefixEnd_1714512 293456247967167065871703 := by
  unfold tailWord_1714512
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266694982311657091244895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41688926643082209454993193 31266694982311657091244895)
  ·
    refine ⟨46900042473467485636867343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31266694982311657091244895 46900042473467485636867343)
    ·
      refine ⟨70350063710201228455301015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46900042473467485636867343 70350063710201228455301015)
      ·
        refine ⟨105525095565301842682951523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70350063710201228455301015 105525095565301842682951523)
        ·
          refine ⟨158287643347952764024427285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105525095565301842682951523 158287643347952764024427285)
          ·
            refine ⟨7419733281935285813645029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158287643347952764024427285 7419733281935285813645029)
            ·
              refine ⟨1391199990362866090058443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7419733281935285813645029 1391199990362866090058443)
              ·
                refine ⟨2086799985544299135087665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391199990362866090058443 2086799985544299135087665)
                ·
                  refine ⟨1565099989158224351315749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086799985544299135087665 1565099989158224351315749)
                  ·
                    refine ⟨293456247967167065871703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1565099989158224351315749 293456247967167065871703)
                    ·
                      rfl

theorem cell23_1714512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_1714512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714512 prefixEnd_1714512 := by exact prefixLift 1714512
  have htrace : WordTrace (prefixWord ++ tailWord_1714512) baseStart_1714512 baseEnd_1714512 := by
    simpa [prefixWord, tailWord_1714512, baseEnd_1714512] using wordTrace_append hprefix tailTrace_1714512
  have hstable : (prefixWord ++ tailWord_1714512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714512).length < 2 ^ (prefixWord ++ tailWord_1714512).sum := by decide
  have hdescent : baseEnd_1714512 < baseStart_1714512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714535 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3]
def baseStart_1714535 : Nat := 118140960795 + 1714535 * 2 ^ 59
def prefixEnd_1714535 : Nat := 4983230072969 + 3 ^ 40 * 1714535 * 2
def baseEnd_1714535 : Nat := 880380553956554607627503

theorem tailTrace_1714535 : CollatzResearch.WordTrace tailWord_1714535 prefixEnd_1714535 880380553956554607627503 := by
  unfold tailWord_1714535
  simp only [CollatzResearch.WordTrace]
  refine ⟨62534228843539989110577059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41689485895693326073718039 62534228843539989110577059)
  ·
    refine ⟨93801343265309983665865589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62534228843539989110577059 93801343265309983665865589)
    ·
      refine ⟨8793875931122810968674899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93801343265309983665865589 8793875931122810968674899)
      ·
        refine ⟨13190813896684216453012349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8793875931122810968674899 13190813896684216453012349)
        ·
          refine ⟨4946555211256581169879631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13190813896684216453012349 4946555211256581169879631)
          ·
            refine ⟨7419832816884871754819447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4946555211256581169879631 7419832816884871754819447)
            ·
              refine ⟨11129749225327307632229171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7419832816884871754819447 11129749225327307632229171)
              ·
                refine ⟨16694623837990961448343757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11129749225327307632229171 16694623837990961448343757)
                ·
                  refine ⟨6260483939246610543128909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16694623837990961448343757 6260483939246610543128909)
                  ·
                    refine ⟨2347681477217478953673341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6260483939246610543128909 2347681477217478953673341)
                    ·
                      refine ⟨880380553956554607627503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2347681477217478953673341 880380553956554607627503)
                      ·
                        rfl

theorem cell23_1714535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_1714535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714535 prefixEnd_1714535 := by exact prefixLift 1714535
  have htrace : WordTrace (prefixWord ++ tailWord_1714535) baseStart_1714535 baseEnd_1714535 := by
    simpa [prefixWord, tailWord_1714535, baseEnd_1714535] using wordTrace_append hprefix tailTrace_1714535
  have hstable : (prefixWord ++ tailWord_1714535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714535).length < 2 ^ (prefixWord ++ tailWord_1714535).sum := by decide
  have hdescent : baseEnd_1714535 < baseStart_1714535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714592 : List Nat := [2, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2]
def baseStart_1714592 : Nat := 118140960795 + 1714592 * 2 ^ 59
def prefixEnd_1714592 : Nat := 4983230072969 + 3 ^ 40 * 1714592 * 2
def baseEnd_1714592 : Nat := 880409822353860884614741

theorem tailTrace_1714592 : CollatzResearch.WordTrace tailWord_1714592 prefixEnd_1714592 880409822353860884614741 := by
  unfold tailWord_1714592
  simp only [CollatzResearch.WordTrace]
  refine ⟨31268153902166743922701015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41690871869555658563601353 31268153902166743922701015)
  ·
    refine ⟨46902230853250115884051523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31268153902166743922701015 46902230853250115884051523)
    ·
      refine ⟨70353346279875173826077285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46902230853250115884051523 70353346279875173826077285)
      ·
        refine ⟨13191252427476595092389491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70353346279875173826077285 13191252427476595092389491)
        ·
          refine ⟨19786878641214892638584237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13191252427476595092389491 19786878641214892638584237)
          ·
            refine ⟨7420079490455584739469089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19786878641214892638584237 7420079490455584739469089)
            ·
              refine ⟨5565059617841688554601817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420079490455584739469089 5565059617841688554601817)
              ·
                refine ⟨4173794713381266415951363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5565059617841688554601817 4173794713381266415951363)
                ·
                  refine ⟨6260692070071899623927045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4173794713381266415951363 6260692070071899623927045)
                  ·
                    refine ⟨1173879763138481179486321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6260692070071899623927045 1173879763138481179486321)
                    ·
                      refine ⟨880409822353860884614741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1173879763138481179486321 880409822353860884614741)
                      ·
                        rfl

theorem cell23_1714592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_1714592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1714592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1714592 prefixEnd_1714592 := by exact prefixLift 1714592
  have htrace : WordTrace (prefixWord ++ tailWord_1714592) baseStart_1714592 baseEnd_1714592 := by
    simpa [prefixWord, tailWord_1714592, baseEnd_1714592] using wordTrace_append hprefix tailTrace_1714592
  have hstable : (prefixWord ++ tailWord_1714592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714592).length < 2 ^ (prefixWord ++ tailWord_1714592).sum := by decide
  have hdescent : baseEnd_1714592 < baseStart_1714592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
