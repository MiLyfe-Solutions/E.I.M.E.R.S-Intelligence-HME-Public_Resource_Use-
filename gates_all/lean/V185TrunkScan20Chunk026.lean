import V185TrunkScan20Chunk025

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_158791 : List Nat := [1, 1, 4, 1, 3, 4, 2, 1, 3]
def baseStart_158791 : Nat := 118140960795 + 158791 * 2 ^ 59
def prefixEnd_158791 : Nat := 4983230072969 + 3 ^ 40 * 158791 * 2
def baseEnd_158791 : Nat := 72476539207283078384213

theorem tailTrace_158791 : CollatzResearch.WordTrace tailWord_158791 prefixEnd_158791 72476539207283078384213 := by
  unfold tailWord_158791
  simp only [CollatzResearch.WordTrace]
  refine ⟨5791583567734801188828227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3861055711823200792552151 5791583567734801188828227)
  ·
    refine ⟨8687375351602201783242341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5791583567734801188828227 8687375351602201783242341)
    ·
      refine ⟨1628882878425412834357939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8687375351602201783242341 1628882878425412834357939)
      ·
        refine ⟨2443324317638119251536909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1628882878425412834357939 2443324317638119251536909)
        ·
          refine ⟨916246619114294719326341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2443324317638119251536909 916246619114294719326341)
          ·
            refine ⟨171796241083930259873689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 916246619114294719326341 171796241083930259873689)
            ·
              refine ⟨128847180812947694905267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171796241083930259873689 128847180812947694905267)
              ·
                refine ⟨193270771219421542357901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128847180812947694905267 193270771219421542357901)
                ·
                  refine ⟨72476539207283078384213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193270771219421542357901 72476539207283078384213)
                  ·
                    rfl

theorem cell20_158791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 1, 3].length) (baseStart_158791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158791 prefixEnd_158791 := by exact prefixLift 158791
  have htrace : WordTrace (prefixWord ++ tailWord_158791) baseStart_158791 baseEnd_158791 := by
    simpa [prefixWord, tailWord_158791, baseEnd_158791] using wordTrace_append hprefix tailTrace_158791
  have hstable : (prefixWord ++ tailWord_158791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158791).length < 2 ^ (prefixWord ++ tailWord_158791).sum := by decide
  have hdescent : baseEnd_158791 < baseStart_158791 := by decide
  rcases family_descends (prefixWord ++ tailWord_158791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158819 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 2]
def baseStart_158819 : Nat := 118140960795 + 158819 * 2 ^ 59
def prefixEnd_158819 : Nat := 4983230072969 + 3 ^ 40 * 158819 * 2
def baseEnd_158819 : Nat := 72489319170239425450765

theorem tailTrace_158819 : CollatzResearch.WordTrace tailWord_158819 prefixEnd_158819 72489319170239425450765 := by
  unfold tailWord_158819
  simp only [CollatzResearch.WordTrace]
  refine ⟨5792604811633361970847511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3861736541088907980565007 5792604811633361970847511)
  ·
    refine ⟨8688907217450042956271267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5792604811633361970847511 8688907217450042956271267)
    ·
      refine ⟨13033360826175064434406901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8688907217450042956271267 13033360826175064434406901)
      ·
        refine ⟨1221877577453912290725647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13033360826175064434406901 1221877577453912290725647)
        ·
          refine ⟨1832816366180868436088471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221877577453912290725647 1832816366180868436088471)
          ·
            refine ⟨2749224549271302654132707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1832816366180868436088471 2749224549271302654132707)
            ·
              refine ⟨4123836823906953981199061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2749224549271302654132707 4123836823906953981199061)
              ·
                refine ⟨96652425560319233934353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4123836823906953981199061 96652425560319233934353)
                ·
                  refine ⟨72489319170239425450765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96652425560319233934353 72489319170239425450765)
                  ·
                    rfl

theorem cell20_158819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 2].length) (baseStart_158819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158819 prefixEnd_158819 := by exact prefixLift 158819
  have htrace : WordTrace (prefixWord ++ tailWord_158819) baseStart_158819 baseEnd_158819 := by
    simpa [prefixWord, tailWord_158819, baseEnd_158819] using wordTrace_append hprefix tailTrace_158819
  have hstable : (prefixWord ++ tailWord_158819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158819).length < 2 ^ (prefixWord ++ tailWord_158819).sum := by decide
  have hdescent : baseEnd_158819 < baseStart_158819 := by decide
  rcases family_descends (prefixWord ++ tailWord_158819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158874 : List Nat := [3, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_158874 : Nat := 118140960795 + 158874 * 2 ^ 59
def prefixEnd_158874 : Nat := 4983230072969 + 3 ^ 40 * 158874 * 2
def baseEnd_158874 : Nat := 72514422668903678617207

theorem tailTrace_158874 : CollatzResearch.WordTrace tailWord_158874 prefixEnd_158874 72514422668903678617207 := by
  unfold tailWord_158874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1448652706608526591024919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3863073884289404242733117 1448652706608526591024919)
  ·
    refine ⟨2172979059912789886537379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1448652706608526591024919 2172979059912789886537379)
    ·
      refine ⟨3259468589869184829806069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2172979059912789886537379 3259468589869184829806069)
      ·
        refine ⟨305575180300236077794319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3259468589869184829806069 305575180300236077794319)
        ·
          refine ⟨458362770450354116691479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305575180300236077794319 458362770450354116691479)
          ·
            refine ⟨687544155675531175037219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458362770450354116691479 687544155675531175037219)
            ·
              refine ⟨1031316233513296762555829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687544155675531175037219 1031316233513296762555829)
              ·
                refine ⟨96685896891871571489609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1031316233513296762555829 96685896891871571489609)
                ·
                  refine ⟨72514422668903678617207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96685896891871571489609 72514422668903678617207)
                  ·
                    rfl

theorem cell20_158874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_158874 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158874 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158874 prefixEnd_158874 := by exact prefixLift 158874
  have htrace : WordTrace (prefixWord ++ tailWord_158874) baseStart_158874 baseEnd_158874 := by
    simpa [prefixWord, tailWord_158874, baseEnd_158874] using wordTrace_append hprefix tailTrace_158874
  have hstable : (prefixWord ++ tailWord_158874).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158874).length < 2 ^ (prefixWord ++ tailWord_158874).sum := by decide
  have hdescent : baseEnd_158874 < baseStart_158874 := by decide
  rcases family_descends (prefixWord ++ tailWord_158874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158885 : List Nat := [1, 3, 1, 2, 1, 5, 7]
def baseStart_158885 : Nat := 118140960795 + 158885 * 2 ^ 59
def prefixEnd_158885 : Nat := 4983230072969 + 3 ^ 40 * 158885 * 2
def baseEnd_158885 : Nat := 8057715929848503250055

theorem tailTrace_158885 : CollatzResearch.WordTrace tailWord_158885 prefixEnd_158885 8057715929848503250055 := by
  unfold tailWord_158885
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795012029394255242750109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3863341352929503495166739 5795012029394255242750109)
  ·
    refine ⟨2173129511022845716031291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5795012029394255242750109 2173129511022845716031291)
    ·
      refine ⟨3259694266534268574046937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2173129511022845716031291 3259694266534268574046937)
      ·
        refine ⟨2444770699900701430535203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3259694266534268574046937 2444770699900701430535203)
        ·
          refine ⟨3667156049851052145802805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444770699900701430535203 3667156049851052145802805)
          ·
            refine ⟨343795879673536138669013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3667156049851052145802805 343795879673536138669013)
            ·
              refine ⟨8057715929848503250055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 343795879673536138669013 8057715929848503250055)
              ·
                rfl

theorem cell20_158885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_158885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158885 prefixEnd_158885 := by exact prefixLift 158885
  have htrace : WordTrace (prefixWord ++ tailWord_158885) baseStart_158885 baseEnd_158885 := by
    simpa [prefixWord, tailWord_158885, baseEnd_158885] using wordTrace_append hprefix tailTrace_158885
  have hstable : (prefixWord ++ tailWord_158885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158885).length < 2 ^ (prefixWord ++ tailWord_158885).sum := by decide
  have hdescent : baseEnd_158885 < baseStart_158885 := by decide
  rcases family_descends (prefixWord ++ tailWord_158885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158895 : List Nat := [1, 1, 2, 1, 2, 3, 4, 4, 2]
def baseStart_158895 : Nat := 118140960795 + 158895 * 2 ^ 59
def prefixEnd_158895 : Nat := 4983230072969 + 3 ^ 40 * 158895 * 2
def baseEnd_158895 : Nat := 72524007641120938917121

theorem tailTrace_158895 : CollatzResearch.WordTrace tailWord_158895 prefixEnd_158895 72524007641120938917121 := by
  unfold tailWord_158895
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795376759358026950614139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3863584506238684633742759 5795376759358026950614139)
  ·
    refine ⟨8693065139037040425921209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5795376759358026950614139 8693065139037040425921209)
    ·
      refine ⟨6519798854277780319440907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8693065139037040425921209 6519798854277780319440907)
      ·
        refine ⟨9779698281416670479161361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519798854277780319440907 9779698281416670479161361)
        ·
          refine ⟨7334773711062502859371021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9779698281416670479161361 7334773711062502859371021)
          ·
            refine ⟨2750540141648438572264133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7334773711062502859371021 2750540141648438572264133)
            ·
              refine ⟨515726276559082232299525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2750540141648438572264133 515726276559082232299525)
              ·
                refine ⟨96698676854827918556161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515726276559082232299525 96698676854827918556161)
                ·
                  refine ⟨72524007641120938917121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96698676854827918556161 72524007641120938917121)
                  ·
                    rfl

theorem cell20_158895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 4, 2].length) (baseStart_158895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158895 prefixEnd_158895 := by exact prefixLift 158895
  have htrace : WordTrace (prefixWord ++ tailWord_158895) baseStart_158895 baseEnd_158895 := by
    simpa [prefixWord, tailWord_158895, baseEnd_158895] using wordTrace_append hprefix tailTrace_158895
  have hstable : (prefixWord ++ tailWord_158895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158895).length < 2 ^ (prefixWord ++ tailWord_158895).sum := by decide
  have hdescent : baseEnd_158895 < baseStart_158895 := by decide
  rcases family_descends (prefixWord ++ tailWord_158895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158909 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 3]
def baseStart_158909 : Nat := 118140960795 + 158909 * 2 ^ 59
def prefixEnd_158909 : Nat := 4983230072969 + 3 ^ 40 * 158909 * 2
def baseEnd_158909 : Nat := 72530397622599112450397

theorem tailTrace_158909 : CollatzResearch.WordTrace tailWord_158909 prefixEnd_158909 72530397622599112450397 := by
  unfold tailWord_158909
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795887381307307341623781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3863924920871538227749187 5795887381307307341623781)
  ·
    refine ⟨1086728883995120126554459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5795887381307307341623781 1086728883995120126554459)
    ·
      refine ⟨1630093325992680189831689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1086728883995120126554459 1630093325992680189831689)
      ·
        refine ⟨1222569994494510142373767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1630093325992680189831689 1222569994494510142373767)
        ·
          refine ⟨1833854991741765213560651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222569994494510142373767 1833854991741765213560651)
          ·
            refine ⟨2750782487612647820340977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1833854991741765213560651 2750782487612647820340977)
            ·
              refine ⟨2063086865709485865255733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2750782487612647820340977 2063086865709485865255733)
              ·
                refine ⟨193414393660264299867725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2063086865709485865255733 193414393660264299867725)
                ·
                  refine ⟨72530397622599112450397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193414393660264299867725 72530397622599112450397)
                  ·
                    rfl

theorem cell20_158909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_158909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158909 prefixEnd_158909 := by exact prefixLift 158909
  have htrace : WordTrace (prefixWord ++ tailWord_158909) baseStart_158909 baseEnd_158909 := by
    simpa [prefixWord, tailWord_158909, baseEnd_158909] using wordTrace_append hprefix tailTrace_158909
  have hstable : (prefixWord ++ tailWord_158909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158909).length < 2 ^ (prefixWord ++ tailWord_158909).sum := by decide
  have hdescent : baseEnd_158909 < baseStart_158909 := by decide
  rcases family_descends (prefixWord ++ tailWord_158909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158925 : List Nat := [1, 6, 2, 2, 1, 2, 1, 3, 2]
def baseStart_158925 : Nat := 118140960795 + 158925 * 2 ^ 59
def prefixEnd_158925 : Nat := 4983230072969 + 3 ^ 40 * 158925 * 2
def baseEnd_158925 : Nat := 72537700458574167916999

theorem tailTrace_158925 : CollatzResearch.WordTrace tailWord_158925 prefixEnd_158925 72537700458574167916999 := by
  unfold tailWord_158925
  simp only [CollatzResearch.WordTrace]
  refine ⟨5796470949249342074206229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3864313966166228049470819 5796470949249342074206229)
  ·
    refine ⟨271709575746062909728417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5796470949249342074206229 271709575746062909728417)
    ·
      refine ⟨203782181809547182296313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271709575746062909728417 203782181809547182296313)
      ·
        refine ⟨152836636357160386722235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203782181809547182296313 152836636357160386722235)
        ·
          refine ⟨229254954535740580083353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152836636357160386722235 229254954535740580083353)
          ·
            refine ⟨171941215901805435062515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229254954535740580083353 171941215901805435062515)
            ·
              refine ⟨257911823852708152593773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171941215901805435062515 257911823852708152593773)
              ·
                refine ⟨96716933944765557222665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257911823852708152593773 96716933944765557222665)
                ·
                  refine ⟨72537700458574167916999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96716933944765557222665 72537700458574167916999)
                  ·
                    rfl

theorem cell20_158925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_158925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_158925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_158925 prefixEnd_158925 := by exact prefixLift 158925
  have htrace : WordTrace (prefixWord ++ tailWord_158925) baseStart_158925 baseEnd_158925 := by
    simpa [prefixWord, tailWord_158925, baseEnd_158925] using wordTrace_append hprefix tailTrace_158925
  have hstable : (prefixWord ++ tailWord_158925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158925).length < 2 ^ (prefixWord ++ tailWord_158925).sum := by decide
  have hdescent : baseEnd_158925 < baseStart_158925 := by decide
  rcases family_descends (prefixWord ++ tailWord_158925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159002 : List Nat := [3, 1, 1, 3, 3, 2, 2, 2, 3]
def baseStart_159002 : Nat := 118140960795 + 159002 * 2 ^ 59
def prefixEnd_159002 : Nat := 4983230072969 + 3 ^ 40 * 159002 * 2
def baseEnd_159002 : Nat := 72572845356704122350017

theorem tailTrace_159002 : CollatzResearch.WordTrace tailWord_159002 prefixEnd_159002 72572845356704122350017 := by
  unfold tailWord_159002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449819842492596056189815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3866186246646922816506173 1449819842492596056189815)
  ·
    refine ⟨2174729763738894084284723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449819842492596056189815 2174729763738894084284723)
    ·
      refine ⟨3262094645608341126427085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174729763738894084284723 3262094645608341126427085)
      ·
        refine ⟨1223285492103127922410157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3262094645608341126427085 1223285492103127922410157)
        ·
          refine ⟨458732059538672970903809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1223285492103127922410157 458732059538672970903809)
          ·
            refine ⟨344049044654004728177857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458732059538672970903809 344049044654004728177857)
            ·
              refine ⟨258036783490503546133393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344049044654004728177857 258036783490503546133393)
              ·
                refine ⟨193527587617877659600045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258036783490503546133393 193527587617877659600045)
                ·
                  refine ⟨72572845356704122350017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193527587617877659600045 72572845356704122350017)
                  ·
                    rfl

theorem cell20_159002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 2, 2, 3].length) (baseStart_159002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159002 prefixEnd_159002 := by exact prefixLift 159002
  have htrace : WordTrace (prefixWord ++ tailWord_159002) baseStart_159002 baseEnd_159002 := by
    simpa [prefixWord, tailWord_159002, baseEnd_159002] using wordTrace_append hprefix tailTrace_159002
  have hstable : (prefixWord ++ tailWord_159002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159002).length < 2 ^ (prefixWord ++ tailWord_159002).sum := by decide
  have hdescent : baseEnd_159002 < baseStart_159002 := by decide
  rcases family_descends (prefixWord ++ tailWord_159002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159005 : List Nat := [1, 4, 2, 3, 1, 1, 4, 2, 2]
def baseStart_159005 : Nat := 118140960795 + 159005 * 2 ^ 59
def prefixEnd_159005 : Nat := 4983230072969 + 3 ^ 40 * 159005 * 2
def baseEnd_159005 : Nat := 72574214638449445250005

theorem tailTrace_159005 : CollatzResearch.WordTrace tailWord_159005 prefixEnd_159005 72574214638449445250005 := by
  unfold tailWord_159005
  simp only [CollatzResearch.WordTrace]
  refine ⟨5799388788959515737118469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3866259192639677158078979 5799388788959515737118469)
  ·
    refine ⟨1087385397929909200709713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5799388788959515737118469 1087385397929909200709713)
    ·
      refine ⟨815539048447431900532285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1087385397929909200709713 815539048447431900532285)
      ·
        refine ⟨305827143167786962699607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 815539048447431900532285 305827143167786962699607)
        ·
          refine ⟨458740714751680444049411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305827143167786962699607 458740714751680444049411)
          ·
            refine ⟨688111072127520666074117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458740714751680444049411 688111072127520666074117)
            ·
              refine ⟨129020826023910124888897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688111072127520666074117 129020826023910124888897)
              ·
                refine ⟨96765619517932593666673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129020826023910124888897 96765619517932593666673)
                ·
                  refine ⟨72574214638449445250005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96765619517932593666673 72574214638449445250005)
                  ·
                    rfl

theorem cell20_159005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_159005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159005 prefixEnd_159005 := by exact prefixLift 159005
  have htrace : WordTrace (prefixWord ++ tailWord_159005) baseStart_159005 baseEnd_159005 := by
    simpa [prefixWord, tailWord_159005, baseEnd_159005] using wordTrace_append hprefix tailTrace_159005
  have hstable : (prefixWord ++ tailWord_159005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159005).length < 2 ^ (prefixWord ++ tailWord_159005).sum := by decide
  have hdescent : baseEnd_159005 < baseStart_159005 := by decide
  rcases family_descends (prefixWord ++ tailWord_159005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159016 : List Nat := [2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_159016 : Nat := 118140960795 + 159016 * 2 ^ 59
def prefixEnd_159016 : Nat := 4983230072969 + 3 ^ 40 * 159016 * 2
def baseEnd_159016 : Nat := 24193078446060765294431

theorem tailTrace_159016 : CollatzResearch.WordTrace tailWord_159016 prefixEnd_159016 24193078446060765294431 := by
  unfold tailWord_159016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899894995959832307884451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3866526661279776410512601 2899894995959832307884451)
  ·
    refine ⟨4349842493939748461826677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899894995959832307884451 4349842493939748461826677)
    ·
      refine ⟨407797733806851418296251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4349842493939748461826677 407797733806851418296251)
      ·
        refine ⟨611696600710277127444377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407797733806851418296251 611696600710277127444377)
        ·
          refine ⟨458772450532707845583283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611696600710277127444377 458772450532707845583283)
          ·
            refine ⟨688158675799061768374925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458772450532707845583283 688158675799061768374925)
            ·
              refine ⟨258059503424648163140597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 688158675799061768374925 258059503424648163140597)
              ·
                refine ⟨24193078446060765294431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258059503424648163140597 24193078446060765294431)
                ·
                  rfl

theorem cell20_159016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_159016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159016 prefixEnd_159016 := by exact prefixLift 159016
  have htrace : WordTrace (prefixWord ++ tailWord_159016) baseStart_159016 baseEnd_159016 := by
    simpa [prefixWord, tailWord_159016, baseEnd_159016] using wordTrace_append hprefix tailTrace_159016
  have hstable : (prefixWord ++ tailWord_159016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159016).length < 2 ^ (prefixWord ++ tailWord_159016).sum := by decide
  have hdescent : baseEnd_159016 < baseStart_159016 := by decide
  rcases family_descends (prefixWord ++ tailWord_159016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159033 : List Nat := [1, 2, 1, 6, 2, 1, 3, 4]
def baseStart_159033 : Nat := 118140960795 + 159033 * 2 ^ 59
def prefixEnd_159033 : Nat := 4983230072969 + 3 ^ 40 * 159033 * 2
def baseEnd_159033 : Nat := 24195664867135264105519

theorem tailTrace_159033 : CollatzResearch.WordTrace tailWord_159033 prefixEnd_159033 24195664867135264105519 := by
  unfold tailWord_159033
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800410032858076519137753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3866940021905384346091835 5800410032858076519137753)
  ·
    refine ⟨4350307524643557389353315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5800410032858076519137753 4350307524643557389353315)
    ·
      refine ⟨6525461286965336084029973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4350307524643557389353315 6525461286965336084029973)
      ·
        refine ⟨305880997826500128938905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6525461286965336084029973 305880997826500128938905)
        ·
          refine ⟨229410748369875096704179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305880997826500128938905 229410748369875096704179)
          ·
            refine ⟨344116122554812645056269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229410748369875096704179 344116122554812645056269)
            ·
              refine ⟨129043545958054741896101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344116122554812645056269 129043545958054741896101)
              ·
                refine ⟨24195664867135264105519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129043545958054741896101 24195664867135264105519)
                ·
                  rfl

theorem cell20_159033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 4].length) (baseStart_159033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159033 prefixEnd_159033 := by exact prefixLift 159033
  have htrace : WordTrace (prefixWord ++ tailWord_159033) baseStart_159033 baseEnd_159033 := by
    simpa [prefixWord, tailWord_159033, baseEnd_159033] using wordTrace_append hprefix tailTrace_159033
  have hstable : (prefixWord ++ tailWord_159033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159033).length < 2 ^ (prefixWord ++ tailWord_159033).sum := by decide
  have hdescent : baseEnd_159033 < baseStart_159033 := by decide
  rcases family_descends (prefixWord ++ tailWord_159033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159047 : List Nat := [1, 1, 4, 1, 2, 3, 1, 5, 2]
def baseStart_159047 : Nat := 118140960795 + 159047 * 2 ^ 59
def prefixEnd_159047 : Nat := 4983230072969 + 3 ^ 40 * 159047 * 2
def baseEnd_159047 : Nat := 72593384582883965849833

theorem tailTrace_159047 : CollatzResearch.WordTrace tailWord_159047 prefixEnd_159047 72593384582883965849833 := by
  unfold tailWord_159047
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800920654807356910147395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3867280436538237940098263 5800920654807356910147395)
  ·
    refine ⟨8701380982211035365221093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800920654807356910147395 8701380982211035365221093)
    ·
      refine ⟨1631508934164569130978955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8701380982211035365221093 1631508934164569130978955)
      ·
        refine ⟨2447263401246853696468433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631508934164569130978955 2447263401246853696468433)
        ·
          refine ⟨1835447550935140272351325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2447263401246853696468433 1835447550935140272351325)
          ·
            refine ⟨688292831600677602131747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1835447550935140272351325 688292831600677602131747)
            ·
              refine ⟨1032439247401016403197621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688292831600677602131747 1032439247401016403197621)
              ·
                refine ⟨96791179443845287799777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1032439247401016403197621 96791179443845287799777)
                ·
                  refine ⟨72593384582883965849833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96791179443845287799777 72593384582883965849833)
                  ·
                    rfl

theorem cell20_159047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 5, 2].length) (baseStart_159047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159047 prefixEnd_159047 := by exact prefixLift 159047
  have htrace : WordTrace (prefixWord ++ tailWord_159047) baseStart_159047 baseEnd_159047 := by
    simpa [prefixWord, tailWord_159047, baseEnd_159047] using wordTrace_append hprefix tailTrace_159047
  have hstable : (prefixWord ++ tailWord_159047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159047).length < 2 ^ (prefixWord ++ tailWord_159047).sum := by decide
  have hdescent : baseEnd_159047 < baseStart_159047 := by decide
  rcases family_descends (prefixWord ++ tailWord_159047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159053 : List Nat := [1, 6, 1, 3, 2, 1, 1, 2, 3]
def baseStart_159053 : Nat := 118140960795 + 159053 * 2 ^ 59
def prefixEnd_159053 : Nat := 4983230072969 + 3 ^ 40 * 159053 * 2
def baseEnd_159053 : Nat := 72596123146374611649809

theorem tailTrace_159053 : CollatzResearch.WordTrace tailWord_159053 prefixEnd_159053 72596123146374611649809 := by
  unfold tailWord_159053
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801139492785619934865813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3867426328523746623243875 5801139492785619934865813)
  ·
    refine ⟨271928413724325934446835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5801139492785619934865813 271928413724325934446835)
    ·
      refine ⟨407892620586488901670253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271928413724325934446835 407892620586488901670253)
      ·
        refine ⟨152959732719933338126345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407892620586488901670253 152959732719933338126345)
        ·
          refine ⟨114719799539950003594759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152959732719933338126345 114719799539950003594759)
          ·
            refine ⟨172079699309925005392139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114719799539950003594759 172079699309925005392139)
            ·
              refine ⟨258119548964887508088209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172079699309925005392139 258119548964887508088209)
              ·
                refine ⟨193589661723665631066157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258119548964887508088209 193589661723665631066157)
                ·
                  refine ⟨72596123146374611649809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193589661723665631066157 72596123146374611649809)
                  ·
                    rfl

theorem cell20_159053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_159053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159053 prefixEnd_159053 := by exact prefixLift 159053
  have htrace : WordTrace (prefixWord ++ tailWord_159053) baseStart_159053 baseEnd_159053 := by
    simpa [prefixWord, tailWord_159053, baseEnd_159053] using wordTrace_append hprefix tailTrace_159053
  have hstable : (prefixWord ++ tailWord_159053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159053).length < 2 ^ (prefixWord ++ tailWord_159053).sum := by decide
  have hdescent : baseEnd_159053 < baseStart_159053 := by decide
  rcases family_descends (prefixWord ++ tailWord_159053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159061 : List Nat := [1, 3, 2, 2, 3, 2, 1, 1, 5]
def baseStart_159061 : Nat := 118140960795 + 159061 * 2 ^ 59
def prefixEnd_159061 : Nat := 4983230072969 + 3 ^ 40 * 159061 * 2
def baseEnd_159061 : Nat := 72599774564362139383109

theorem tailTrace_159061 : CollatzResearch.WordTrace tailWord_159061 prefixEnd_159061 72599774564362139383109 := by
  unfold tailWord_159061
  simp only [CollatzResearch.WordTrace]
  refine ⟨5801431276756637301157037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3867620851171091534104691 5801431276756637301157037)
  ·
    refine ⟨2175536728783738987933889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5801431276756637301157037 2175536728783738987933889)
    ·
      refine ⟨1631652546587804240950417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2175536728783738987933889 1631652546587804240950417)
      ·
        refine ⟨1223739409940853180712813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1631652546587804240950417 1223739409940853180712813)
        ·
          refine ⟨458902278727819942767305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1223739409940853180712813 458902278727819942767305)
          ·
            refine ⟨344176709045864957075479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458902278727819942767305 344176709045864957075479)
            ·
              refine ⟨516265063568797435613219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344176709045864957075479 516265063568797435613219)
              ·
                refine ⟨774397595353196153419829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516265063568797435613219 774397595353196153419829)
                ·
                  refine ⟨72599774564362139383109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 774397595353196153419829 72599774564362139383109)
                  ·
                    rfl

theorem cell20_159061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_159061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159061 prefixEnd_159061 := by exact prefixLift 159061
  have htrace : WordTrace (prefixWord ++ tailWord_159061) baseStart_159061 baseEnd_159061 := by
    simpa [prefixWord, tailWord_159061, baseEnd_159061] using wordTrace_append hprefix tailTrace_159061
  have hstable : (prefixWord ++ tailWord_159061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159061).length < 2 ^ (prefixWord ++ tailWord_159061).sum := by decide
  have hdescent : baseEnd_159061 < baseStart_159061 := by decide
  rcases family_descends (prefixWord ++ tailWord_159061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159133 : List Nat := [1, 4, 2, 1, 3, 3, 2, 1, 3]
def baseStart_159133 : Nat := 118140960795 + 159133 * 2 ^ 59
def prefixEnd_159133 : Nat := 4983230072969 + 3 ^ 40 * 159133 * 2
def baseEnd_159133 : Nat := 72632637326249888982815

theorem tailTrace_159133 : CollatzResearch.WordTrace tailWord_159133 prefixEnd_159133 72632637326249888982815 := by
  unfold tailWord_159133
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804057332495793597778053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3869371554997195731852035 5804057332495793597778053)
  ·
    refine ⟨1088260749842961299583385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5804057332495793597778053 1088260749842961299583385)
    ·
      refine ⟨816195562382220974687539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1088260749842961299583385 816195562382220974687539)
      ·
        refine ⟨1224293343573331462031309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816195562382220974687539 1224293343573331462031309)
        ·
          refine ⟨459110003839999298261741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1224293343573331462031309 459110003839999298261741)
          ·
            refine ⟨172166251439999736848153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 459110003839999298261741 172166251439999736848153)
            ·
              refine ⟨129124688579999802636115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172166251439999736848153 129124688579999802636115)
              ·
                refine ⟨193687032869999703954173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129124688579999802636115 193687032869999703954173)
                ·
                  refine ⟨72632637326249888982815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193687032869999703954173 72632637326249888982815)
                  ·
                    rfl

theorem cell20_159133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_159133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159133 prefixEnd_159133 := by exact prefixLift 159133
  have htrace : WordTrace (prefixWord ++ tailWord_159133) baseStart_159133 baseEnd_159133 := by
    simpa [prefixWord, tailWord_159133, baseEnd_159133] using wordTrace_append hprefix tailTrace_159133
  have hstable : (prefixWord ++ tailWord_159133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159133).length < 2 ^ (prefixWord ++ tailWord_159133).sum := by decide
  have hdescent : baseEnd_159133 < baseStart_159133 := by decide
  rcases family_descends (prefixWord ++ tailWord_159133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159175 : List Nat := [1, 1, 4, 1, 1, 3, 4, 2, 3]
def baseStart_159175 : Nat := 118140960795 + 159175 * 2 ^ 59
def prefixEnd_159175 : Nat := 4983230072969 + 3 ^ 40 * 159175 * 2
def baseEnd_159175 : Nat := 72651807270684409582643

theorem tailTrace_159175 : CollatzResearch.WordTrace tailWord_159175 prefixEnd_159175 72651807270684409582643 := by
  unfold tailWord_159175
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805589198343634770806979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3870392798895756513871319 5805589198343634770806979)
  ·
    refine ⟨8708383797515452156210469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805589198343634770806979 8708383797515452156210469)
    ·
      refine ⟨1632821962034147279289463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8708383797515452156210469 1632821962034147279289463)
      ·
        refine ⟨2449232943051220918934195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632821962034147279289463 2449232943051220918934195)
        ·
          refine ⟨3673849414576831378401293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449232943051220918934195 3673849414576831378401293)
          ·
            refine ⟨1377693530466311766900485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3673849414576831378401293 1377693530466311766900485)
            ·
              refine ⟨258317536962433456293841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1377693530466311766900485 258317536962433456293841)
              ·
                refine ⟨193738152721825092220381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258317536962433456293841 193738152721825092220381)
                ·
                  refine ⟨72651807270684409582643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193738152721825092220381 72651807270684409582643)
                  ·
                    rfl

theorem cell20_159175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_159175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159175 prefixEnd_159175 := by exact prefixLift 159175
  have htrace : WordTrace (prefixWord ++ tailWord_159175) baseStart_159175 baseEnd_159175 := by
    simpa [prefixWord, tailWord_159175, baseEnd_159175] using wordTrace_append hprefix tailTrace_159175
  have hstable : (prefixWord ++ tailWord_159175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159175).length < 2 ^ (prefixWord ++ tailWord_159175).sum := by decide
  have hdescent : baseEnd_159175 < baseStart_159175 := by decide
  rcases family_descends (prefixWord ++ tailWord_159175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159178 : List Nat := [3, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_159178 : Nat := 118140960795 + 159178 * 2 ^ 59
def prefixEnd_159178 : Nat := 4983230072969 + 3 ^ 40 * 159178 * 2
def baseEnd_159178 : Nat := 72653176552429732482631

theorem tailTrace_159178 : CollatzResearch.WordTrace tailWord_159178 prefixEnd_159178 72653176552429732482631 := by
  unfold tailWord_159178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451424654333191570791547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3870465744888510855444125 1451424654333191570791547)
  ·
    refine ⟨2177136981499787356187321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1451424654333191570791547 2177136981499787356187321)
    ·
      refine ⟨1632852736124840517140491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2177136981499787356187321 1632852736124840517140491)
      ·
        refine ⟨2449279104187260775710737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632852736124840517140491 2449279104187260775710737)
        ·
          refine ⟨1836959328140445581783053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449279104187260775710737 1836959328140445581783053)
          ·
            refine ⟨688859748052667093168645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1836959328140445581783053 688859748052667093168645)
            ·
              refine ⟨129161202759875079969121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688859748052667093168645 129161202759875079969121)
              ·
                refine ⟨96870902069906309976841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129161202759875079969121 96870902069906309976841)
                ·
                  refine ⟨72653176552429732482631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96870902069906309976841 72653176552429732482631)
                  ·
                    rfl

theorem cell20_159178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_159178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159178 prefixEnd_159178 := by exact prefixLift 159178
  have htrace : WordTrace (prefixWord ++ tailWord_159178) baseStart_159178 baseEnd_159178 := by
    simpa [prefixWord, tailWord_159178, baseEnd_159178] using wordTrace_append hprefix tailTrace_159178
  have hstable : (prefixWord ++ tailWord_159178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159178).length < 2 ^ (prefixWord ++ tailWord_159178).sum := by decide
  have hdescent : baseEnd_159178 < baseStart_159178 := by decide
  rcases family_descends (prefixWord ++ tailWord_159178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159265 : List Nat := [1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_159265 : Nat := 118140960795 + 159265 * 2 ^ 59
def prefixEnd_159265 : Nat := 4983230072969 + 3 ^ 40 * 159265 * 2
def baseEnd_159265 : Nat := 24230961907681365527425

theorem tailTrace_159265 : CollatzResearch.WordTrace tailWord_159265 prefixEnd_159265 24230961907681365527425 := by
  unfold tailWord_159265
  simp only [CollatzResearch.WordTrace]
  refine ⟨5808871768017580141583249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3872581178678386761055499 5808871768017580141583249)
  ·
    refine ⟨4356653826013185106187437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5808871768017580141583249 4356653826013185106187437)
    ·
      refine ⟨1633745184754944414820289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4356653826013185106187437 1633745184754944414820289)
      ·
        refine ⟨1225308888566208311115217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1633745184754944414820289 1225308888566208311115217)
        ·
          refine ⟨918981666424656233336413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225308888566208311115217 918981666424656233336413)
          ·
            refine ⟨344618124909246087501155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 918981666424656233336413 344618124909246087501155)
            ·
              refine ⟨516927187363869131251733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344618124909246087501155 516927187363869131251733)
              ·
                refine ⟨24230961907681365527425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 516927187363869131251733 24230961907681365527425)
                ·
                  rfl

theorem cell20_159265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_159265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159265 prefixEnd_159265 := by exact prefixLift 159265
  have htrace : WordTrace (prefixWord ++ tailWord_159265) baseStart_159265 baseEnd_159265 := by
    simpa [prefixWord, tailWord_159265, baseEnd_159265] using wordTrace_append hprefix tailTrace_159265
  have hstable : (prefixWord ++ tailWord_159265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159265).length < 2 ^ (prefixWord ++ tailWord_159265).sum := by decide
  have hdescent : baseEnd_159265 < baseStart_159265 := by decide
  rcases family_descends (prefixWord ++ tailWord_159265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159292 : List Nat := [2, 2, 2, 2, 5, 1, 1, 1, 4]
def baseStart_159292 : Nat := 118140960795 + 159292 * 2 ^ 59
def prefixEnd_159292 : Nat := 4983230072969 + 3 ^ 40 * 159292 * 2
def baseEnd_159292 : Nat := 72705209258752002682165

theorem tailTrace_159292 : CollatzResearch.WordTrace tailWord_159292 prefixEnd_159292 72705209258752002682165 := by
  unfold tailWord_159292
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904928269459881876408065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3873237692613175835210753 2904928269459881876408065)
  ·
    refine ⟨2178696202094911407306049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2904928269459881876408065 2178696202094911407306049)
    ·
      refine ⟨1634022151571183555479537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2178696202094911407306049 1634022151571183555479537)
      ·
        refine ⟨1225516613678387666609653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1634022151571183555479537 1225516613678387666609653)
        ·
          refine ⟨114892182532348843744655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1225516613678387666609653 114892182532348843744655)
          ·
            refine ⟨172338273798523265616983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114892182532348843744655 172338273798523265616983)
            ·
              refine ⟨258507410697784898425475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172338273798523265616983 258507410697784898425475)
              ·
                refine ⟨387761116046677347638213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258507410697784898425475 387761116046677347638213)
                ·
                  refine ⟨72705209258752002682165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387761116046677347638213 72705209258752002682165)
                  ·
                    rfl

theorem cell20_159292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_159292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159292 prefixEnd_159292 := by exact prefixLift 159292
  have htrace : WordTrace (prefixWord ++ tailWord_159292) baseStart_159292 baseEnd_159292 := by
    simpa [prefixWord, tailWord_159292, baseEnd_159292] using wordTrace_append hprefix tailTrace_159292
  have hstable : (prefixWord ++ tailWord_159292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159292).length < 2 ^ (prefixWord ++ tailWord_159292).sum := by decide
  have hdescent : baseEnd_159292 < baseStart_159292 := by decide
  rcases family_descends (prefixWord ++ tailWord_159292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159317 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_159317 : Nat := 118140960795 + 159317 * 2 ^ 59
def prefixEnd_159317 : Nat := 4983230072969 + 3 ^ 40 * 159317 * 2
def baseEnd_159317 : Nat := 72716619939963026848729

theorem tailTrace_159317 : CollatzResearch.WordTrace tailWord_159317 prefixEnd_159317 72716619939963026848729 := by
  unfold tailWord_159317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5810768363829193022476205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3873845575886128681650803 5810768363829193022476205)
  ·
    refine ⟨2179038136435947383428577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5810768363829193022476205 2179038136435947383428577)
    ·
      refine ⟨1634278602326960537571433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2179038136435947383428577 1634278602326960537571433)
      ·
        refine ⟨1225708951745220403178575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1634278602326960537571433 1225708951745220403178575)
        ·
          refine ⟨1838563427617830604767863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225708951745220403178575 1838563427617830604767863)
          ·
            refine ⟨2757845141426745907151795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1838563427617830604767863 2757845141426745907151795)
            ·
              refine ⟨4136767712140118860727693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2757845141426745907151795 4136767712140118860727693)
              ·
                refine ⟨1551287892052544572772885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4136767712140118860727693 1551287892052544572772885)
                ·
                  refine ⟨72716619939963026848729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1551287892052544572772885 72716619939963026848729)
                  ·
                    rfl

theorem cell20_159317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_159317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159317 prefixEnd_159317 := by exact prefixLift 159317
  have htrace : WordTrace (prefixWord ++ tailWord_159317) baseStart_159317 baseEnd_159317 := by
    simpa [prefixWord, tailWord_159317, baseEnd_159317] using wordTrace_append hprefix tailTrace_159317
  have hstable : (prefixWord ++ tailWord_159317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159317).length < 2 ^ (prefixWord ++ tailWord_159317).sum := by decide
  have hdescent : baseEnd_159317 < baseStart_159317 := by decide
  rcases family_descends (prefixWord ++ tailWord_159317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159341 : List Nat := [1, 5, 1, 1, 4, 8]
def baseStart_159341 : Nat := 118140960795 + 159341 * 2 ^ 59
def prefixEnd_159341 : Nat := 4983230072969 + 3 ^ 40 * 159341 * 2
def baseEnd_159341 : Nat := 2693613859034281853653

theorem tailTrace_159341 : CollatzResearch.WordTrace tailWord_159341 prefixEnd_159341 2693613859034281853653 := by
  unfold tailWord_159341
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811643715742245121349877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3874429143828163414233251 5811643715742245121349877)
  ·
    refine ⟨544841598350835480126551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5811643715742245121349877 544841598350835480126551)
    ·
      refine ⟨817262397526253220189827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544841598350835480126551 817262397526253220189827)
      ·
        refine ⟨1225893596289379830284741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 817262397526253220189827 1225893596289379830284741)
        ·
          refine ⟨229855049304258718178389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1225893596289379830284741 229855049304258718178389)
          ·
            refine ⟨2693613859034281853653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 229855049304258718178389 2693613859034281853653)
            ·
              rfl

theorem cell20_159341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 8].length) (baseStart_159341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159341 prefixEnd_159341 := by exact prefixLift 159341
  have htrace : WordTrace (prefixWord ++ tailWord_159341) baseStart_159341 baseEnd_159341 := by
    simpa [prefixWord, tailWord_159341, baseEnd_159341] using wordTrace_append hprefix tailTrace_159341
  have hstable : (prefixWord ++ tailWord_159341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159341).length < 2 ^ (prefixWord ++ tailWord_159341).sum := by decide
  have hdescent : baseEnd_159341 < baseStart_159341 := by decide
  rcases family_descends (prefixWord ++ tailWord_159341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159355 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_159355 : Nat := 118140960795 + 159355 * 2 ^ 59
def prefixEnd_159355 : Nat := 4983230072969 + 3 ^ 40 * 159355 * 2
def baseEnd_159355 : Nat := 72733964175403783581907

theorem tailTrace_159355 : CollatzResearch.WordTrace tailWord_159355 prefixEnd_159355 72733964175403783581907 := by
  unfold tailWord_159355
  simp only [CollatzResearch.WordTrace]
  refine ⟨5812154337691525512359519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3874769558461017008239679 5812154337691525512359519)
  ·
    refine ⟨8718231506537288268539279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5812154337691525512359519 8718231506537288268539279)
    ·
      refine ⟨13077347259805932402808919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8718231506537288268539279 13077347259805932402808919)
      ·
        refine ⟨19616020889708898604213379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13077347259805932402808919 19616020889708898604213379)
        ·
          refine ⟨29424031334563347906320069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19616020889708898604213379 29424031334563347906320069)
          ·
            refine ⟨5517005875230627732435013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29424031334563347906320069 5517005875230627732435013)
            ·
              refine ⟨1034438601605742699831565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5517005875230627732435013 1034438601605742699831565)
              ·
                refine ⟨387914475602153512436837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1034438601605742699831565 387914475602153512436837)
                ·
                  refine ⟨72733964175403783581907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 387914475602153512436837 72733964175403783581907)
                  ·
                    rfl

theorem cell20_159355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_159355 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159355 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159355 prefixEnd_159355 := by exact prefixLift 159355
  have htrace : WordTrace (prefixWord ++ tailWord_159355) baseStart_159355 baseEnd_159355 := by
    simpa [prefixWord, tailWord_159355, baseEnd_159355] using wordTrace_append hprefix tailTrace_159355
  have hstable : (prefixWord ++ tailWord_159355).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159355).length < 2 ^ (prefixWord ++ tailWord_159355).sum := by decide
  have hdescent : baseEnd_159355 < baseStart_159355 := by decide
  rcases family_descends (prefixWord ++ tailWord_159355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159406 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_159406 : Nat := 118140960795 + 159406 * 2 ^ 59
def prefixEnd_159406 : Nat := 4983230072969 + 3 ^ 40 * 159406 * 2
def baseEnd_159406 : Nat := 72757241965074272881699

theorem tailTrace_159406 : CollatzResearch.WordTrace tailWord_159406 prefixEnd_159406 72757241965074272881699 := by
  unfold tailWord_159406
  simp only [CollatzResearch.WordTrace]
  refine ⟨726751807563345152808259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3876009640337840814977381 726751807563345152808259)
  ·
    refine ⟨1090127711345017729212389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 726751807563345152808259 1090127711345017729212389)
    ·
      refine ⟨204398945877190824227323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1090127711345017729212389 204398945877190824227323)
      ·
        refine ⟨306598418815786236340985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204398945877190824227323 306598418815786236340985)
        ·
          refine ⟨229948814111839677255739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306598418815786236340985 229948814111839677255739)
          ·
            refine ⟨344923221167759515883609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229948814111839677255739 344923221167759515883609)
            ·
              refine ⟨258692415875819636912707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 344923221167759515883609 258692415875819636912707)
              ·
                refine ⟨388038623813729455369061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 258692415875819636912707 388038623813729455369061)
                ·
                  refine ⟨72757241965074272881699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388038623813729455369061 72757241965074272881699)
                  ·
                    rfl

theorem cell20_159406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_159406 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159406 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159406 prefixEnd_159406 := by exact prefixLift 159406
  have htrace : WordTrace (prefixWord ++ tailWord_159406) baseStart_159406 baseEnd_159406 := by
    simpa [prefixWord, tailWord_159406, baseEnd_159406] using wordTrace_append hprefix tailTrace_159406
  have hstable : (prefixWord ++ tailWord_159406).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159406).length < 2 ^ (prefixWord ++ tailWord_159406).sum := by decide
  have hdescent : baseEnd_159406 < baseStart_159406 := by decide
  rcases family_descends (prefixWord ++ tailWord_159406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159420 : List Nat := [2, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_159420 : Nat := 118140960795 + 159420 * 2 ^ 59
def prefixEnd_159420 : Nat := 4983230072969 + 3 ^ 40 * 159420 * 2
def baseEnd_159420 : Nat := 72763631946552446414975

theorem tailTrace_159420 : CollatzResearch.WordTrace tailWord_159420 prefixEnd_159420 72763631946552446414975 := by
  unfold tailWord_159420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907262541228020806737857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3876350054970694408983809 2907262541228020806737857)
  ·
    refine ⟨2180446905921015605053393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2907262541228020806737857 2180446905921015605053393)
    ·
      refine ⟨1635335179440761703790045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2180446905921015605053393 1635335179440761703790045)
      ·
        refine ⟨613250692290285638921267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1635335179440761703790045 613250692290285638921267)
        ·
          refine ⟨919876038435428458381901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613250692290285638921267 919876038435428458381901)
          ·
            refine ⟨344953514413285671893213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 919876038435428458381901 344953514413285671893213)
            ·
              refine ⟨129357567904982126959955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344953514413285671893213 129357567904982126959955)
              ·
                refine ⟨194036351857473190439933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129357567904982126959955 194036351857473190439933)
                ·
                  refine ⟨72763631946552446414975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194036351857473190439933 72763631946552446414975)
                  ·
                    rfl

theorem cell20_159420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_159420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159420 prefixEnd_159420 := by exact prefixLift 159420
  have htrace : WordTrace (prefixWord ++ tailWord_159420) baseStart_159420 baseEnd_159420 := by
    simpa [prefixWord, tailWord_159420, baseEnd_159420] using wordTrace_append hprefix tailTrace_159420
  have hstable : (prefixWord ++ tailWord_159420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159420).length < 2 ^ (prefixWord ++ tailWord_159420).sum := by decide
  have hdescent : baseEnd_159420 < baseStart_159420 := by decide
  rcases family_descends (prefixWord ++ tailWord_159420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159426 : List Nat := [3, 5, 1, 2, 2, 1, 2, 4]
def baseStart_159426 : Nat := 118140960795 + 159426 * 2 ^ 59
def prefixEnd_159426 : Nat := 4983230072969 + 3 ^ 40 * 159426 * 2
def baseEnd_159426 : Nat := 24255456836681030738317

theorem tailTrace_159426 : CollatzResearch.WordTrace tailWord_159426 prefixEnd_159426 24255456836681030738317 := by
  unfold tailWord_159426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453685980108576159548533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3876495946956203092129421 1453685980108576159548533)
  ·
    refine ⟨136283060635179014957675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1453685980108576159548533 136283060635179014957675)
    ·
      refine ⟨204424590952768522436513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136283060635179014957675 204424590952768522436513)
      ·
        refine ⟨153318443214576391827385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 204424590952768522436513 153318443214576391827385)
        ·
          refine ⟨114988832410932293870539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153318443214576391827385 114988832410932293870539)
          ·
            refine ⟨172483248616398440805809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114988832410932293870539 172483248616398440805809)
            ·
              refine ⟨129362436462298830604357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172483248616398440805809 129362436462298830604357)
              ·
                refine ⟨24255456836681030738317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129362436462298830604357 24255456836681030738317)
                ·
                  rfl

theorem cell20_159426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_159426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159426 prefixEnd_159426 := by exact prefixLift 159426
  have htrace : WordTrace (prefixWord ++ tailWord_159426) baseStart_159426 baseEnd_159426 := by
    simpa [prefixWord, tailWord_159426, baseEnd_159426] using wordTrace_append hprefix tailTrace_159426
  have hstable : (prefixWord ++ tailWord_159426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159426).length < 2 ^ (prefixWord ++ tailWord_159426).sum := by decide
  have hdescent : baseEnd_159426 < baseStart_159426 := by decide
  rcases family_descends (prefixWord ++ tailWord_159426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159430 : List Nat := [6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_159430 : Nat := 118140960795 + 159430 * 2 ^ 59
def prefixEnd_159430 : Nat := 4983230072969 + 3 ^ 40 * 159430 * 2
def baseEnd_159430 : Nat := 24256065406345618693867

theorem tailTrace_159430 : CollatzResearch.WordTrace tailWord_159430 prefixEnd_159430 24256065406345618693867 := by
  unfold tailWord_159430
  simp only [CollatzResearch.WordTrace]
  refine ⟨181715306638119166291867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3876593208279875547559829 181715306638119166291867)
  ·
    refine ⟨272572959957178749437801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181715306638119166291867 272572959957178749437801)
    ·
      refine ⟨204429719967884062078351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272572959957178749437801 204429719967884062078351)
      ·
        refine ⟨306644579951826093117527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204429719967884062078351 306644579951826093117527)
        ·
          refine ⟨459966869927739139676291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306644579951826093117527 459966869927739139676291)
          ·
            refine ⟨689950304891608709514437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459966869927739139676291 689950304891608709514437)
            ·
              refine ⟨129365682167176633033957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 689950304891608709514437 129365682167176633033957)
              ·
                refine ⟨24256065406345618693867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129365682167176633033957 24256065406345618693867)
                ·
                  rfl

theorem cell20_159430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_159430 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159430 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159430 prefixEnd_159430 := by exact prefixLift 159430
  have htrace : WordTrace (prefixWord ++ tailWord_159430) baseStart_159430 baseEnd_159430 := by
    simpa [prefixWord, tailWord_159430, baseEnd_159430] using wordTrace_append hprefix tailTrace_159430
  have hstable : (prefixWord ++ tailWord_159430).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159430).length < 2 ^ (prefixWord ++ tailWord_159430).sum := by decide
  have hdescent : baseEnd_159430 < baseStart_159430 := by decide
  rcases family_descends (prefixWord ++ tailWord_159430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159431 : List Nat := [1, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_159431 : Nat := 118140960795 + 159431 * 2 ^ 59
def prefixEnd_159431 : Nat := 4983230072969 + 3 ^ 40 * 159431 * 2
def baseEnd_159431 : Nat := 72768652646285297048263

theorem tailTrace_159431 : CollatzResearch.WordTrace tailWord_159431 prefixEnd_159431 72768652646285297048263 := by
  unfold tailWord_159431
  simp only [CollatzResearch.WordTrace]
  refine ⟨5814926285416190492126147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3876617523610793661417431 5814926285416190492126147)
  ·
    refine ⟨8722389428124285738189221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5814926285416190492126147 8722389428124285738189221)
    ·
      refine ⟨1635448017773303575910479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8722389428124285738189221 1635448017773303575910479)
      ·
        refine ⟨2453172026659955363865719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1635448017773303575910479 2453172026659955363865719)
        ·
          refine ⟨3679758039989933045798579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2453172026659955363865719 3679758039989933045798579)
          ·
            refine ⟨5519637059984899568697869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3679758039989933045798579 5519637059984899568697869)
            ·
              refine ⟨2069863897494337338261701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5519637059984899568697869 2069863897494337338261701)
              ·
                refine ⟨388099480780188250924069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2069863897494337338261701 388099480780188250924069)
                ·
                  refine ⟨72768652646285297048263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388099480780188250924069 72768652646285297048263)
                  ·
                    rfl

theorem cell20_159431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_159431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159431 prefixEnd_159431 := by exact prefixLift 159431
  have htrace : WordTrace (prefixWord ++ tailWord_159431) baseStart_159431 baseEnd_159431 := by
    simpa [prefixWord, tailWord_159431, baseEnd_159431] using wordTrace_append hprefix tailTrace_159431
  have hstable : (prefixWord ++ tailWord_159431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159431).length < 2 ^ (prefixWord ++ tailWord_159431).sum := by decide
  have hdescent : baseEnd_159431 < baseStart_159431 := by decide
  rcases family_descends (prefixWord ++ tailWord_159431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159444 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 2]
def baseStart_159444 : Nat := 118140960795 + 159444 * 2 ^ 59
def prefixEnd_159444 : Nat := 4983230072969 + 3 ^ 40 * 159444 * 2
def baseEnd_159444 : Nat := 72774586200515029614877

theorem tailTrace_159444 : CollatzResearch.WordTrace tailWord_159444 prefixEnd_159444 72774586200515029614877 := by
  unfold tailWord_159444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2907700217184546856174693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3876933622912729141566257 2907700217184546856174693)
  ·
    refine ⟨545193790722102535532755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2907700217184546856174693 545193790722102535532755)
    ·
      refine ⟨817790686083153803299133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545193790722102535532755 817790686083153803299133)
      ·
        refine ⟨306671507281182676237175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 817790686083153803299133 306671507281182676237175)
        ·
          refine ⟨460007260921774014355763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306671507281182676237175 460007260921774014355763)
          ·
            refine ⟨690010891382661021533645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 460007260921774014355763 690010891382661021533645)
            ·
              refine ⟨258754084268497883075117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 690010891382661021533645 258754084268497883075117)
              ·
                refine ⟨97032781600686706153169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258754084268497883075117 97032781600686706153169)
                ·
                  refine ⟨72774586200515029614877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97032781600686706153169 72774586200515029614877)
                  ·
                    rfl

theorem cell20_159444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_159444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159444 prefixEnd_159444 := by exact prefixLift 159444
  have htrace : WordTrace (prefixWord ++ tailWord_159444) baseStart_159444 baseEnd_159444 := by
    simpa [prefixWord, tailWord_159444, baseEnd_159444] using wordTrace_append hprefix tailTrace_159444
  have hstable : (prefixWord ++ tailWord_159444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159444).length < 2 ^ (prefixWord ++ tailWord_159444).sum := by decide
  have hdescent : baseEnd_159444 < baseStart_159444 := by decide
  rcases family_descends (prefixWord ++ tailWord_159444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159479 : List Nat := [1, 1, 3, 1, 1, 1, 8, 1, 3]
def baseStart_159479 : Nat := 118140960795 + 159479 * 2 ^ 59
def prefixEnd_159479 : Nat := 4983230072969 + 3 ^ 40 * 159479 * 2
def baseEnd_159479 : Nat := 72790561154210463448067

theorem tailTrace_159479 : CollatzResearch.WordTrace tailWord_159479 prefixEnd_159479 72790561154210463448067 := by
  unfold tailWord_159479
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816676989242294689873491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3877784659494863126582327 5816676989242294689873491)
  ·
    refine ⟨8725015483863442034810237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816676989242294689873491 8725015483863442034810237)
    ·
      refine ⟨3271880806448790763053839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8725015483863442034810237 3271880806448790763053839)
      ·
        refine ⟨4907821209673186144580759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271880806448790763053839 4907821209673186144580759)
        ·
          refine ⟨7361731814509779216871139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907821209673186144580759 7361731814509779216871139)
          ·
            refine ⟨11042597721764668825306709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7361731814509779216871139 11042597721764668825306709)
            ·
              refine ⟨129405442051929712796563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 11042597721764668825306709 129405442051929712796563)
              ·
                refine ⟨194108163077894569194845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129405442051929712796563 194108163077894569194845)
                ·
                  refine ⟨72790561154210463448067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194108163077894569194845 72790561154210463448067)
                  ·
                    rfl

theorem cell20_159479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 1, 3].length) (baseStart_159479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159479 prefixEnd_159479 := by exact prefixLift 159479
  have htrace : WordTrace (prefixWord ++ tailWord_159479) baseStart_159479 baseEnd_159479 := by
    simpa [prefixWord, tailWord_159479, baseEnd_159479] using wordTrace_append hprefix tailTrace_159479
  have hstable : (prefixWord ++ tailWord_159479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159479).length < 2 ^ (prefixWord ++ tailWord_159479).sum := by decide
  have hdescent : baseEnd_159479 < baseStart_159479 := by decide
  rcases family_descends (prefixWord ++ tailWord_159479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159483 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 7]
def baseStart_159483 : Nat := 118140960795 + 159483 * 2 ^ 59
def prefixEnd_159483 : Nat := 4983230072969 + 3 ^ 40 * 159483 * 2
def baseEnd_159483 : Nat := 72792386863204227314717

theorem tailTrace_159483 : CollatzResearch.WordTrace tailWord_159483 prefixEnd_159483 72792386863204227314717 := by
  unfold tailWord_159483
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816822881227803373019103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3877881920818535582012735 5816822881227803373019103)
  ·
    refine ⟨8725234321841705059528655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816822881227803373019103 8725234321841705059528655)
    ·
      refine ⟨13087851482762557589292983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8725234321841705059528655 13087851482762557589292983)
      ·
        refine ⟨19631777224143836383939475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13087851482762557589292983 19631777224143836383939475)
        ·
          refine ⟨29447665836215754575909213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19631777224143836383939475 29447665836215754575909213)
          ·
            refine ⟨11042874688580907965965955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29447665836215754575909213 11042874688580907965965955)
            ·
              refine ⟨16564312032871361948948933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11042874688580907965965955 16564312032871361948948933)
              ·
                refine ⟨3105808506163380365427925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16564312032871361948948933 3105808506163380365427925)
                ·
                  refine ⟨72792386863204227314717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3105808506163380365427925 72792386863204227314717)
                  ·
                    rfl

theorem cell20_159483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_159483 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159483 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159483 prefixEnd_159483 := by exact prefixLift 159483
  have htrace : WordTrace (prefixWord ++ tailWord_159483) baseStart_159483 baseEnd_159483 := by
    simpa [prefixWord, tailWord_159483, baseEnd_159483] using wordTrace_append hprefix tailTrace_159483
  have hstable : (prefixWord ++ tailWord_159483).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159483).length < 2 ^ (prefixWord ++ tailWord_159483).sum := by decide
  have hdescent : baseEnd_159483 < baseStart_159483 := by decide
  rcases family_descends (prefixWord ++ tailWord_159483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159514 : List Nat := [3, 1, 1, 3, 2, 10]
def baseStart_159514 : Nat := 118140960795 + 159514 * 2 ^ 59
def prefixEnd_159514 : Nat := 4983230072969 + 3 ^ 40 * 159514 * 2
def baseEnd_159514 : Nat := 2696538374366885084491

theorem tailTrace_159514 : CollatzResearch.WordTrace tailWord_159514 prefixEnd_159514 2696538374366885084491 := by
  unfold tailWord_159514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1454488386028873916849399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3878635696076997111598397 1454488386028873916849399)
  ·
    refine ⟨2181732579043310875274099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1454488386028873916849399 2181732579043310875274099)
    ·
      refine ⟨3272598868564966312911149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2181732579043310875274099 3272598868564966312911149)
      ·
        refine ⟨1227224575711862367341681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3272598868564966312911149 1227224575711862367341681)
        ·
          refine ⟨920418431783896775506261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1227224575711862367341681 920418431783896775506261)
          ·
            refine ⟨2696538374366885084491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 920418431783896775506261 2696538374366885084491)
            ·
              rfl

theorem cell20_159514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 10].length) (baseStart_159514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159514 prefixEnd_159514 := by exact prefixLift 159514
  have htrace : WordTrace (prefixWord ++ tailWord_159514) baseStart_159514 baseEnd_159514 := by
    simpa [prefixWord, tailWord_159514, baseEnd_159514] using wordTrace_append hprefix tailTrace_159514
  have hstable : (prefixWord ++ tailWord_159514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159514).length < 2 ^ (prefixWord ++ tailWord_159514).sum := by decide
  have hdescent : baseEnd_159514 < baseStart_159514 := by decide
  rcases family_descends (prefixWord ++ tailWord_159514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159572 : List Nat := [2, 4, 1, 1, 3, 3, 1, 2, 3]
def baseStart_159572 : Nat := 118140960795 + 159572 * 2 ^ 59
def prefixEnd_159572 : Nat := 4983230072969 + 3 ^ 40 * 159572 * 2
def baseEnd_159572 : Nat := 72833008888315473347687

theorem tailTrace_159572 : CollatzResearch.WordTrace tailWord_159572 prefixEnd_159572 72833008888315473347687 := by
  unfold tailWord_159572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910034488952685786504485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3880045985270247715339313 2910034488952685786504485)
  ·
    refine ⟨545631466678628584969591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2910034488952685786504485 545631466678628584969591)
    ·
      refine ⟨818447200017942877454387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 545631466678628584969591 818447200017942877454387)
      ·
        refine ⟨1227670800026914316181581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818447200017942877454387 1227670800026914316181581)
        ·
          refine ⟨460376550010092868568093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1227670800026914316181581 460376550010092868568093)
          ·
            refine ⟨172641206253784825713035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460376550010092868568093 172641206253784825713035)
            ·
              refine ⟨258961809380677238569553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172641206253784825713035 258961809380677238569553)
              ·
                refine ⟨194221357035507928927165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 258961809380677238569553 194221357035507928927165)
                ·
                  refine ⟨72833008888315473347687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194221357035507928927165 72833008888315473347687)
                  ·
                    rfl

theorem cell20_159572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_159572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159572 prefixEnd_159572 := by exact prefixLift 159572
  have htrace : WordTrace (prefixWord ++ tailWord_159572) baseStart_159572 baseEnd_159572 := by
    simpa [prefixWord, tailWord_159572, baseEnd_159572] using wordTrace_append hprefix tailTrace_159572
  have hstable : (prefixWord ++ tailWord_159572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159572).length < 2 ^ (prefixWord ++ tailWord_159572).sum := by decide
  have hdescent : baseEnd_159572 < baseStart_159572 := by decide
  rcases family_descends (prefixWord ++ tailWord_159572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159583 : List Nat := [1, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_159583 : Nat := 118140960795 + 159583 * 2 ^ 59
def prefixEnd_159583 : Nat := 4983230072969 + 3 ^ 40 * 159583 * 2
def baseEnd_159583 : Nat := 72838029588048323980975

theorem tailTrace_159583 : CollatzResearch.WordTrace tailWord_159583 prefixEnd_159583 72838029588048323980975 := by
  unfold tailWord_159583
  simp only [CollatzResearch.WordTrace]
  refine ⟨5820470180865520451659403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3880313453910346967772935 5820470180865520451659403)
  ·
    refine ⟨8730705271298280677489105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5820470180865520451659403 8730705271298280677489105)
    ·
      refine ⟨6548028953473710508116829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8730705271298280677489105 6548028953473710508116829)
      ·
        refine ⟨2455510857552641440543811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6548028953473710508116829 2455510857552641440543811)
        ·
          refine ⟨3683266286328962160815717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2455510857552641440543811 3683266286328962160815717)
          ·
            refine ⟨690612428686680405152947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3683266286328962160815717 690612428686680405152947)
            ·
              refine ⟨1035918643030020607729421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 690612428686680405152947 1035918643030020607729421)
              ·
                refine ⟨388469491136257727898533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1035918643030020607729421 388469491136257727898533)
                ·
                  refine ⟨72838029588048323980975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 388469491136257727898533 72838029588048323980975)
                  ·
                    rfl

theorem cell20_159583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_159583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159583 prefixEnd_159583 := by exact prefixLift 159583
  have htrace : WordTrace (prefixWord ++ tailWord_159583) baseStart_159583 baseEnd_159583 := by
    simpa [prefixWord, tailWord_159583, baseEnd_159583] using wordTrace_append hprefix tailTrace_159583
  have hstable : (prefixWord ++ tailWord_159583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159583).length < 2 ^ (prefixWord ++ tailWord_159583).sum := by decide
  have hdescent : baseEnd_159583 < baseStart_159583 := by decide
  rcases family_descends (prefixWord ++ tailWord_159583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159624 : List Nat := [2, 1, 3, 3, 4, 1, 6]
def baseStart_159624 : Nat := 118140960795 + 159624 * 2 ^ 59
def prefixEnd_159624 : Nat := 4983230072969 + 3 ^ 40 * 159624 * 2
def baseEnd_159624 : Nat := 8095193678359378179349

theorem tailTrace_159624 : CollatzResearch.WordTrace tailWord_159624 prefixEnd_159624 8095193678359378179349 := by
  unfold tailWord_159624
  simp only [CollatzResearch.WordTrace]
  refine ⟨2910982786858492226950963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3881310382477989635934617 2910982786858492226950963)
  ·
    refine ⟨4366474180287738340426445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2910982786858492226950963 4366474180287738340426445)
    ·
      refine ⟨1637427817607901877659917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4366474180287738340426445 1637427817607901877659917)
      ·
        refine ⟨614035431602963204122469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1637427817607901877659917 614035431602963204122469)
        ·
          refine ⟨115131643425555600772963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 614035431602963204122469 115131643425555600772963)
          ·
            refine ⟨172697465138333401159445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115131643425555600772963 172697465138333401159445)
            ·
              refine ⟨8095193678359378179349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 172697465138333401159445 8095193678359378179349)
              ·
                rfl

theorem cell20_159624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 6].length) (baseStart_159624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159624 prefixEnd_159624 := by exact prefixLift 159624
  have htrace : WordTrace (prefixWord ++ tailWord_159624) baseStart_159624 baseEnd_159624 := by
    simpa [prefixWord, tailWord_159624, baseEnd_159624] using wordTrace_append hprefix tailTrace_159624
  have hstable : (prefixWord ++ tailWord_159624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159624).length < 2 ^ (prefixWord ++ tailWord_159624).sum := by decide
  have hdescent : baseEnd_159624 < baseStart_159624 := by decide
  rcases family_descends (prefixWord ++ tailWord_159624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159645 : List Nat := [1, 4, 2, 1, 2, 3, 2, 5]
def baseStart_159645 : Nat := 118140960795 + 159645 * 2 ^ 59
def prefixEnd_159645 : Nat := 4983230072969 + 3 ^ 40 * 159645 * 2
def baseEnd_159645 : Nat := 24288776025817221304685

theorem tailTrace_159645 : CollatzResearch.WordTrace tailWord_159645 prefixEnd_159645 24288776025817221304685 := by
  unfold tailWord_159645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5822731506640905040416389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3881821004427270026944259 5822731506640905040416389)
  ·
    refine ⟨1091762157495169695078073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5822731506640905040416389 1091762157495169695078073)
    ·
      refine ⟨818821618121377271308555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1091762157495169695078073 818821618121377271308555)
      ·
        refine ⟨1228232427182065906962833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818821618121377271308555 1228232427182065906962833)
        ·
          refine ⟨921174320386549430222125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1228232427182065906962833 921174320386549430222125)
          ·
            refine ⟨345440370144956036333297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 921174320386549430222125 345440370144956036333297)
            ·
              refine ⟨259080277608717027249973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345440370144956036333297 259080277608717027249973)
              ·
                refine ⟨24288776025817221304685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259080277608717027249973 24288776025817221304685)
                ·
                  rfl

theorem cell20_159645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 5].length) (baseStart_159645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159645 prefixEnd_159645 := by exact prefixLift 159645
  have htrace : WordTrace (prefixWord ++ tailWord_159645) baseStart_159645 baseEnd_159645 := by
    simpa [prefixWord, tailWord_159645, baseEnd_159645] using wordTrace_append hprefix tailTrace_159645
  have hstable : (prefixWord ++ tailWord_159645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159645).length < 2 ^ (prefixWord ++ tailWord_159645).sum := by decide
  have hdescent : baseEnd_159645 < baseStart_159645 := by decide
  rcases family_descends (prefixWord ++ tailWord_159645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159690 : List Nat := [3, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_159690 : Nat := 118140960795 + 159690 * 2 ^ 59
def prefixEnd_159690 : Nat := 4983230072969 + 3 ^ 40 * 159690 * 2
def baseEnd_159690 : Nat := 72886867303631507413871

theorem tailTrace_159690 : CollatzResearch.WordTrace tailWord_159690 prefixEnd_159690 72886867303631507413871 := by
  unfold tailWord_159690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456093197869469431451131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3882915194318585150536349 1456093197869469431451131)
  ·
    refine ⟨2184139796804204147176697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1456093197869469431451131 2184139796804204147176697)
    ·
      refine ⟨1638104847603153110382523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2184139796804204147176697 1638104847603153110382523)
      ·
        refine ⟨2457157271404729665573785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1638104847603153110382523 2457157271404729665573785)
        ·
          refine ⟨1842867953553547249180339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2457157271404729665573785 1842867953553547249180339)
          ·
            refine ⟨2764301930330320873770509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1842867953553547249180339 2764301930330320873770509)
            ·
              refine ⟨1036613223873870327663941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2764301930330320873770509 1036613223873870327663941)
              ·
                refine ⟨194364979476350686436989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1036613223873870327663941 194364979476350686436989)
                ·
                  refine ⟨72886867303631507413871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194364979476350686436989 72886867303631507413871)
                  ·
                    rfl

theorem cell20_159690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_159690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159690 prefixEnd_159690 := by exact prefixLift 159690
  have htrace : WordTrace (prefixWord ++ tailWord_159690) baseStart_159690 baseEnd_159690 := by
    simpa [prefixWord, tailWord_159690, baseEnd_159690] using wordTrace_append hprefix tailTrace_159690
  have hstable : (prefixWord ++ tailWord_159690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159690).length < 2 ^ (prefixWord ++ tailWord_159690).sum := by decide
  have hdescent : baseEnd_159690 < baseStart_159690 := by decide
  rcases family_descends (prefixWord ++ tailWord_159690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159752 : List Nat := [2, 1, 3, 2, 1, 2, 1, 6, 2]
def baseStart_159752 : Nat := 118140960795 + 159752 * 2 ^ 59
def prefixEnd_159752 : Nat := 4983230072969 + 3 ^ 40 * 159752 * 2
def baseEnd_159752 : Nat := 72915165793034847346951

theorem tailTrace_159752 : CollatzResearch.WordTrace tailWord_159752 prefixEnd_159752 72915165793034847346951 := by
  unfold tailWord_159752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2913317058626631157280755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3884422744835508209707673 2913317058626631157280755)
  ·
    refine ⟨4369975587939946735921133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2913317058626631157280755 4369975587939946735921133)
    ·
      refine ⟨1638740845477480025970425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4369975587939946735921133 1638740845477480025970425)
      ·
        refine ⟨1229055634108110019477819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1638740845477480025970425 1229055634108110019477819)
        ·
          refine ⟨1843583451162165029216729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1229055634108110019477819 1843583451162165029216729)
          ·
            refine ⟨1382687588371623771912547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1843583451162165029216729 1382687588371623771912547)
            ·
              refine ⟨2074031382557435657868821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1382687588371623771912547 2074031382557435657868821)
              ·
                refine ⟨97220221057379796462601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2074031382557435657868821 97220221057379796462601)
                ·
                  refine ⟨72915165793034847346951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97220221057379796462601 72915165793034847346951)
                  ·
                    rfl

theorem cell20_159752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 2].length) (baseStart_159752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159752 prefixEnd_159752 := by exact prefixLift 159752
  have htrace : WordTrace (prefixWord ++ tailWord_159752) baseStart_159752 baseEnd_159752 := by
    simpa [prefixWord, tailWord_159752, baseEnd_159752] using wordTrace_append hprefix tailTrace_159752
  have hstable : (prefixWord ++ tailWord_159752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159752).length < 2 ^ (prefixWord ++ tailWord_159752).sum := by decide
  have hdescent : baseEnd_159752 < baseStart_159752 := by decide
  rcases family_descends (prefixWord ++ tailWord_159752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159786 : List Nat := [3, 1, 4, 1, 2, 3, 1, 3, 2]
def baseStart_159786 : Nat := 118140960795 + 159786 * 2 ^ 59
def prefixEnd_159786 : Nat := 4983230072969 + 3 ^ 40 * 159786 * 2
def baseEnd_159786 : Nat := 72930684319481840213479

theorem tailTrace_159786 : CollatzResearch.WordTrace tailWord_159786 prefixEnd_159786 72930684319481840213479 := by
  unfold tailWord_159786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456968549782521530324803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3885249466086724080866141 1456968549782521530324803)
  ·
    refine ⟨2185452824673782295487205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1456968549782521530324803 2185452824673782295487205)
    ·
      refine ⟨409772404626334180403851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2185452824673782295487205 409772404626334180403851)
      ·
        refine ⟨614658606939501270605777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409772404626334180403851 614658606939501270605777)
        ·
          refine ⟨460993955204625952954333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614658606939501270605777 460993955204625952954333)
          ·
            refine ⟨172872733201734732357875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460993955204625952954333 172872733201734732357875)
            ·
              refine ⟨259309099802602098536813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172872733201734732357875 259309099802602098536813)
              ·
                refine ⟨97240912425975786951305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259309099802602098536813 97240912425975786951305)
                ·
                  refine ⟨72930684319481840213479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97240912425975786951305 72930684319481840213479)
                  ·
                    rfl

theorem cell20_159786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 1, 3, 2].length) (baseStart_159786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159786 prefixEnd_159786 := by exact prefixLift 159786
  have htrace : WordTrace (prefixWord ++ tailWord_159786) baseStart_159786 baseEnd_159786 := by
    simpa [prefixWord, tailWord_159786, baseEnd_159786] using wordTrace_append hprefix tailTrace_159786
  have hstable : (prefixWord ++ tailWord_159786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159786).length < 2 ^ (prefixWord ++ tailWord_159786).sum := by decide
  have hdescent : baseEnd_159786 < baseStart_159786 := by decide
  rcases family_descends (prefixWord ++ tailWord_159786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159804 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 3]
def baseStart_159804 : Nat := 118140960795 + 159804 * 2 ^ 59
def prefixEnd_159804 : Nat := 4983230072969 + 3 ^ 40 * 159804 * 2
def baseEnd_159804 : Nat := 72938900009953777613405

theorem tailTrace_159804 : CollatzResearch.WordTrace tailWord_159804 prefixEnd_159804 72938900009953777613405 := by
  unfold tailWord_159804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914265356532437597727233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3885687142043250130302977 2914265356532437597727233)
  ·
    refine ⟨2185699017399328198295425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2914265356532437597727233 2185699017399328198295425)
    ·
      refine ⟨1639274263049496148721569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2185699017399328198295425 1639274263049496148721569)
      ·
        refine ⟨1229455697287122111541177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1639274263049496148721569 1229455697287122111541177)
        ·
          refine ⟨922091772965341583655883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1229455697287122111541177 922091772965341583655883)
          ·
            refine ⟨1383137659448012375483825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922091772965341583655883 1383137659448012375483825)
            ·
              refine ⟨1037353244586009281612869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1383137659448012375483825 1037353244586009281612869)
              ·
                refine ⟨194503733359876740302413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1037353244586009281612869 194503733359876740302413)
                ·
                  refine ⟨72938900009953777613405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194503733359876740302413 72938900009953777613405)
                  ·
                    rfl

theorem cell20_159804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_159804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159804 prefixEnd_159804 := by exact prefixLift 159804
  have htrace : WordTrace (prefixWord ++ tailWord_159804) baseStart_159804 baseEnd_159804 := by
    simpa [prefixWord, tailWord_159804, baseEnd_159804] using wordTrace_append hprefix tailTrace_159804
  have hstable : (prefixWord ++ tailWord_159804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159804).length < 2 ^ (prefixWord ++ tailWord_159804).sum := by decide
  have hdescent : baseEnd_159804 < baseStart_159804 := by decide
  rcases family_descends (prefixWord ++ tailWord_159804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159814 : List Nat := [6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_159814 : Nat := 118140960795 + 159814 * 2 ^ 59
def prefixEnd_159814 : Nat := 4983230072969 + 3 ^ 40 * 159814 * 2
def baseEnd_159814 : Nat := 24314488094146062426677

theorem tailTrace_159814 : CollatzResearch.WordTrace tailWord_159814 prefixEnd_159814 24314488094146062426677 := by
  unfold tailWord_159814
  simp only [CollatzResearch.WordTrace]
  refine ⟨182152982594645215728703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3885930295352431268878997 182152982594645215728703)
  ·
    refine ⟨273229473891967823593055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182152982594645215728703 273229473891967823593055)
    ·
      refine ⟨409844210837951735389583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273229473891967823593055 409844210837951735389583)
      ·
        refine ⟨614766316256927603084375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409844210837951735389583 614766316256927603084375)
        ·
          refine ⟨922149474385391404626563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614766316256927603084375 922149474385391404626563)
          ·
            refine ⟨1383224211578087106939845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922149474385391404626563 1383224211578087106939845)
            ·
              refine ⟨259354539670891332551221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1383224211578087106939845 259354539670891332551221)
              ·
                refine ⟨24314488094146062426677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259354539670891332551221 24314488094146062426677)
                ·
                  rfl

theorem cell20_159814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_159814 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159814 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159814 prefixEnd_159814 := by exact prefixLift 159814
  have htrace : WordTrace (prefixWord ++ tailWord_159814) baseStart_159814 baseEnd_159814 := by
    simpa [prefixWord, tailWord_159814, baseEnd_159814] using wordTrace_append hprefix tailTrace_159814
  have hstable : (prefixWord ++ tailWord_159814).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159814).length < 2 ^ (prefixWord ++ tailWord_159814).sum := by decide
  have hdescent : baseEnd_159814 < baseStart_159814 := by decide
  rcases family_descends (prefixWord ++ tailWord_159814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159821 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 3]
def baseStart_159821 : Nat := 118140960795 + 159821 * 2 ^ 59
def prefixEnd_159821 : Nat := 4983230072969 + 3 ^ 40 * 159821 * 2
def baseEnd_159821 : Nat := 72946659273177274046669

theorem tailTrace_159821 : CollatzResearch.WordTrace tailWord_159821 prefixEnd_159821 72946659273177274046669 := by
  unfold tailWord_159821
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829150754003287098823317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3886100502668858065882211 5829150754003287098823317)
  ·
    refine ⟨273241441593904082757343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5829150754003287098823317 273241441593904082757343)
    ·
      refine ⟨409862162390856124136015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 273241441593904082757343 409862162390856124136015)
      ·
        refine ⟨614793243586284186204023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409862162390856124136015 614793243586284186204023)
        ·
          refine ⟨922189865379426279306035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614793243586284186204023 922189865379426279306035)
          ·
            refine ⟨1383284798069139418959053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922189865379426279306035 1383284798069139418959053)
            ·
              refine ⟨518731799275927282109645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1383284798069139418959053 518731799275927282109645)
              ·
                refine ⟨194524424728472730791117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 518731799275927282109645 194524424728472730791117)
                ·
                  refine ⟨72946659273177274046669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194524424728472730791117 72946659273177274046669)
                  ·
                    rfl

theorem cell20_159821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_159821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159821 prefixEnd_159821 := by exact prefixLift 159821
  have htrace : WordTrace (prefixWord ++ tailWord_159821) baseStart_159821 baseEnd_159821 := by
    simpa [prefixWord, tailWord_159821, baseEnd_159821] using wordTrace_append hprefix tailTrace_159821
  have hstable : (prefixWord ++ tailWord_159821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159821).length < 2 ^ (prefixWord ++ tailWord_159821).sum := by decide
  have hdescent : baseEnd_159821 < baseStart_159821 := by decide
  rcases family_descends (prefixWord ++ tailWord_159821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159862 : List Nat := [5, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_159862 : Nat := 118140960795 + 159862 * 2 ^ 59
def prefixEnd_159862 : Nat := 4983230072969 + 3 ^ 40 * 159862 * 2
def baseEnd_159862 : Nat := 72965372790363353679835

theorem tailTrace_159862 : CollatzResearch.WordTrace tailWord_159862 prefixEnd_159862 72965372790363353679835 := by
  unfold tailWord_159862
  simp only [CollatzResearch.WordTrace]
  refine ⟨364415384178421943816615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3887097431236500734043893 364415384178421943816615)
  ·
    refine ⟨546623076267632915724923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 364415384178421943816615 546623076267632915724923)
    ·
      refine ⟨819934614401449373587385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 546623076267632915724923 819934614401449373587385)
      ·
        refine ⟨614950960801087030190539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819934614401449373587385 614950960801087030190539)
        ·
          refine ⟨922426441201630545285809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614950960801087030190539 922426441201630545285809)
          ·
            refine ⟨691819830901222908964357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922426441201630545285809 691819830901222908964357)
            ·
              refine ⟨129716218293979295430817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 691819830901222908964357 129716218293979295430817)
              ·
                refine ⟨97287163720484471573113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129716218293979295430817 97287163720484471573113)
                ·
                  refine ⟨72965372790363353679835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97287163720484471573113 72965372790363353679835)
                  ·
                    rfl

theorem cell20_159862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_159862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159862 prefixEnd_159862 := by exact prefixLift 159862
  have htrace : WordTrace (prefixWord ++ tailWord_159862) baseStart_159862 baseEnd_159862 := by
    simpa [prefixWord, tailWord_159862, baseEnd_159862] using wordTrace_append hprefix tailTrace_159862
  have hstable : (prefixWord ++ tailWord_159862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159862).length < 2 ^ (prefixWord ++ tailWord_159862).sum := by decide
  have hdescent : baseEnd_159862 < baseStart_159862 := by decide
  rcases family_descends (prefixWord ++ tailWord_159862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159904 : List Nat := [2, 1, 1, 4, 2, 2, 1, 5, 2]
def baseStart_159904 : Nat := 118140960795 + 159904 * 2 ^ 59
def prefixEnd_159904 : Nat := 4983230072969 + 3 ^ 40 * 159904 * 2
def baseEnd_159904 : Nat := 72984542734797874279663

theorem tailTrace_159904 : CollatzResearch.WordTrace tailWord_159904 prefixEnd_159904 72984542734797874279663 := by
  unfold tailWord_159904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916089006351296137047383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3888118675135061516063177 2916089006351296137047383)
  ·
    refine ⟨4374133509526944205571075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2916089006351296137047383 4374133509526944205571075)
    ·
      refine ⟨6561200264290416308356613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4374133509526944205571075 6561200264290416308356613)
      ·
        refine ⟨1230225049554453057816865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6561200264290416308356613 1230225049554453057816865)
        ·
          refine ⟨922668787165839793362649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230225049554453057816865 922668787165839793362649)
          ·
            refine ⟨692001590374379845021987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 922668787165839793362649 692001590374379845021987)
            ·
              refine ⟨1038002385561569767532981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692001590374379845021987 1038002385561569767532981)
              ·
                refine ⟨97312723646397165706217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1038002385561569767532981 97312723646397165706217)
                ·
                  refine ⟨72984542734797874279663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97312723646397165706217 72984542734797874279663)
                  ·
                    rfl

theorem cell20_159904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_159904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159904 prefixEnd_159904 := by exact prefixLift 159904
  have htrace : WordTrace (prefixWord ++ tailWord_159904) baseStart_159904 baseEnd_159904 := by
    simpa [prefixWord, tailWord_159904, baseEnd_159904] using wordTrace_append hprefix tailTrace_159904
  have hstable : (prefixWord ++ tailWord_159904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159904).length < 2 ^ (prefixWord ++ tailWord_159904).sum := by decide
  have hdescent : baseEnd_159904 < baseStart_159904 := by decide
  rcases family_descends (prefixWord ++ tailWord_159904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159911 : List Nat := [1, 1, 6, 2, 2, 1, 7]
def baseStart_159911 : Nat := 118140960795 + 159911 * 2 ^ 59
def prefixEnd_159911 : Nat := 4983230072969 + 3 ^ 40 * 159911 * 2
def baseEnd_159911 : Nat := 8109748636170773449589

theorem tailTrace_159911 : CollatzResearch.WordTrace tailWord_159911 prefixEnd_159911 8109748636170773449589 := by
  unfold tailWord_159911
  simp only [CollatzResearch.WordTrace]
  refine ⟨5832433323677232469599587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3888288882451488313066391 5832433323677232469599587)
  ·
    refine ⟨8748649985515848704399381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5832433323677232469599587 8748649985515848704399381)
    ·
      refine ⟨410092968071055408018721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8748649985515848704399381 410092968071055408018721)
      ·
        refine ⟨307569726053291556014041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410092968071055408018721 307569726053291556014041)
        ·
          refine ⟨230677294539968667010531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307569726053291556014041 230677294539968667010531)
          ·
            refine ⟨346015941809953000515797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230677294539968667010531 346015941809953000515797)
            ·
              refine ⟨8109748636170773449589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 346015941809953000515797 8109748636170773449589)
              ·
                rfl

theorem cell20_159911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 7].length) (baseStart_159911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159911 prefixEnd_159911 := by exact prefixLift 159911
  have htrace : WordTrace (prefixWord ++ tailWord_159911) baseStart_159911 baseEnd_159911 := by
    simpa [prefixWord, tailWord_159911, baseEnd_159911] using wordTrace_append hprefix tailTrace_159911
  have hstable : (prefixWord ++ tailWord_159911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159911).length < 2 ^ (prefixWord ++ tailWord_159911).sum := by decide
  have hdescent : baseEnd_159911 < baseStart_159911 := by decide
  rcases family_descends (prefixWord ++ tailWord_159911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159994 : List Nat := [3, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_159994 : Nat := 118140960795 + 159994 * 2 ^ 59
def prefixEnd_159994 : Nat := 4983230072969 + 3 ^ 40 * 159994 * 2
def baseEnd_159994 : Nat := 73025621187157561279295

theorem tailTrace_159994 : CollatzResearch.WordTrace tailWord_159994 prefixEnd_159994 73025621187157561279295 := by
  unfold tailWord_159994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458865145594134411217759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3890307054917691763247357 1458865145594134411217759)
  ·
    refine ⟨2188297718391201616826639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1458865145594134411217759 2188297718391201616826639)
    ·
      refine ⟨3282446577586802425239959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188297718391201616826639 3282446577586802425239959)
      ·
        refine ⟨4923669866380203637859939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3282446577586802425239959 4923669866380203637859939)
        ·
          refine ⟨7385504799570305456789909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4923669866380203637859939 7385504799570305456789909)
          ·
            refine ⟨346195537479858068287027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7385504799570305456789909 346195537479858068287027)
            ·
              refine ⟨519293306219787102430541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346195537479858068287027 519293306219787102430541)
              ·
                refine ⟨194734989832420163411453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 519293306219787102430541 194734989832420163411453)
                ·
                  refine ⟨73025621187157561279295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194734989832420163411453 73025621187157561279295)
                  ·
                    rfl

theorem cell20_159994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_159994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_159994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_159994 prefixEnd_159994 := by exact prefixLift 159994
  have htrace : WordTrace (prefixWord ++ tailWord_159994) baseStart_159994 baseEnd_159994 := by
    simpa [prefixWord, tailWord_159994, baseEnd_159994] using wordTrace_append hprefix tailTrace_159994
  have hstable : (prefixWord ++ tailWord_159994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159994).length < 2 ^ (prefixWord ++ tailWord_159994).sum := by decide
  have hdescent : baseEnd_159994 < baseStart_159994 := by decide
  rcases family_descends (prefixWord ++ tailWord_159994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160008 : List Nat := [2, 1, 3, 2, 3, 1, 2, 6]
def baseStart_160008 : Nat := 118140960795 + 160008 * 2 ^ 59
def prefixEnd_160008 : Nat := 4983230072969 + 3 ^ 40 * 160008 * 2
def baseEnd_160008 : Nat := 24344003722878578270857

theorem tailTrace_160008 : CollatzResearch.WordTrace tailWord_160008 prefixEnd_160008 24344003722878578270857 := by
  unfold tailWord_160008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917985602162909017940339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3890647469550545357253785 2917985602162909017940339)
  ·
    refine ⟨4376978403244363526910509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2917985602162909017940339 4376978403244363526910509)
    ·
      refine ⟨1641366901216636322591441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4376978403244363526910509 1641366901216636322591441)
      ·
        refine ⟨1231025175912477241943581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1641366901216636322591441 1231025175912477241943581)
        ·
          refine ⟨461634440967178965728843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231025175912477241943581 461634440967178965728843)
          ·
            refine ⟨692451661450768448593265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461634440967178965728843 692451661450768448593265)
            ·
              refine ⟨519338746088076336444949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 692451661450768448593265 519338746088076336444949)
              ·
                refine ⟨24344003722878578270857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 519338746088076336444949 24344003722878578270857)
                ·
                  rfl

theorem cell20_160008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_160008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160008 prefixEnd_160008 := by exact prefixLift 160008
  have htrace : WordTrace (prefixWord ++ tailWord_160008) baseStart_160008 baseEnd_160008 := by
    simpa [prefixWord, tailWord_160008, baseEnd_160008] using wordTrace_append hprefix tailTrace_160008
  have hstable : (prefixWord ++ tailWord_160008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160008).length < 2 ^ (prefixWord ++ tailWord_160008).sum := by decide
  have hdescent : baseEnd_160008 < baseStart_160008 := by decide
  rcases family_descends (prefixWord ++ tailWord_160008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160032 : List Nat := [2, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_160032 : Nat := 118140960795 + 160032 * 2 ^ 59
def prefixEnd_160032 : Nat := 4983230072969 + 3 ^ 40 * 160032 * 2
def baseEnd_160032 : Nat := 73042965422598318012473

theorem tailTrace_160032 : CollatzResearch.WordTrace tailWord_160032 prefixEnd_160032 73042965422598318012473 := by
  unfold tailWord_160032
  simp only [CollatzResearch.WordTrace]
  refine ⟨2918423278119435067377175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3891231037492580089836233 2918423278119435067377175)
  ·
    refine ⟨4377634917179152601065763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2918423278119435067377175 4377634917179152601065763)
    ·
      refine ⟨6566452375768728901598645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4377634917179152601065763 6566452375768728901598645)
      ·
        refine ⟨615604910228318334524873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6566452375768728901598645 615604910228318334524873)
        ·
          refine ⟨461703682671238750893655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 615604910228318334524873 461703682671238750893655)
          ·
            refine ⟨692555524006858126340483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461703682671238750893655 692555524006858126340483)
            ·
              refine ⟨1038833286010287189510725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692555524006858126340483 1038833286010287189510725)
              ·
                refine ⟨194781241126928848033261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1038833286010287189510725 194781241126928848033261)
                ·
                  refine ⟨73042965422598318012473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194781241126928848033261 73042965422598318012473)
                  ·
                    rfl

theorem cell20_160032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_160032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160032 prefixEnd_160032 := by exact prefixLift 160032
  have htrace : WordTrace (prefixWord ++ tailWord_160032) baseStart_160032 baseEnd_160032 := by
    simpa [prefixWord, tailWord_160032, baseEnd_160032] using wordTrace_append hprefix tailTrace_160032
  have hstable : (prefixWord ++ tailWord_160032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160032).length < 2 ^ (prefixWord ++ tailWord_160032).sum := by decide
  have hdescent : baseEnd_160032 < baseStart_160032 := by decide
  rcases family_descends (prefixWord ++ tailWord_160032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160042 : List Nat := [3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_160042 : Nat := 118140960795 + 160042 * 2 ^ 59
def prefixEnd_160042 : Nat := 4983230072969 + 3 ^ 40 * 160042 * 2
def baseEnd_160042 : Nat := 24349176565027575893033

theorem tailTrace_160042 : CollatzResearch.WordTrace tailWord_160042 prefixEnd_160042 24349176565027575893033 := by
  unfold tailWord_160042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459302821550660460654595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3891474190801761228412253 1459302821550660460654595)
  ·
    refine ⟨2188954232325990690981893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1459302821550660460654595 2188954232325990690981893)
    ·
      refine ⟨410428918561123254559105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2188954232325990690981893 410428918561123254559105)
      ·
        refine ⟨307821688920842440919329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410428918561123254559105 307821688920842440919329)
        ·
          refine ⟨230866266690631830689497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307821688920842440919329 230866266690631830689497)
          ·
            refine ⟨173149700017973873017123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230866266690631830689497 173149700017973873017123)
            ·
              refine ⟨259724550026960809525685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173149700017973873017123 259724550026960809525685)
              ·
                refine ⟨24349176565027575893033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259724550026960809525685 24349176565027575893033)
                ·
                  rfl

theorem cell20_160042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_160042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160042 prefixEnd_160042 := by exact prefixLift 160042
  have htrace : WordTrace (prefixWord ++ tailWord_160042) baseStart_160042 baseEnd_160042 := by
    simpa [prefixWord, tailWord_160042, baseEnd_160042] using wordTrace_append hprefix tailTrace_160042
  have hstable : (prefixWord ++ tailWord_160042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160042).length < 2 ^ (prefixWord ++ tailWord_160042).sum := by decide
  have hdescent : baseEnd_160042 < baseStart_160042 := by decide
  rcases family_descends (prefixWord ++ tailWord_160042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160067 : List Nat := [1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_160067 : Nat := 118140960795 + 160067 * 2 ^ 59
def prefixEnd_160067 : Nat := 4983230072969 + 3 ^ 40 * 160067 * 2
def baseEnd_160067 : Nat := 24352980125431250615221

theorem tailTrace_160067 : CollatzResearch.WordTrace tailWord_160067 prefixEnd_160067 24352980125431250615221 := by
  unfold tailWord_160067
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838123111112071112278455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3892082074074714074852303 5838123111112071112278455)
  ·
    refine ⟨8757184666668106668417683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5838123111112071112278455 8757184666668106668417683)
    ·
      refine ⟨13135777000002160002626525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8757184666668106668417683 13135777000002160002626525)
      ·
        refine ⟨4925916375000810000984947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13135777000002160002626525 4925916375000810000984947)
        ·
          refine ⟨7388874562501215001477421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4925916375000810000984947 7388874562501215001477421)
          ·
            refine ⟨2770827960937955625554033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7388874562501215001477421 2770827960937955625554033)
            ·
              refine ⟨2078120970703466719165525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2770827960937955625554033 2078120970703466719165525)
              ·
                refine ⟨24352980125431250615221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2078120970703466719165525 24352980125431250615221)
                ·
                  rfl

theorem cell20_160067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_160067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160067 prefixEnd_160067 := by exact prefixLift 160067
  have htrace : WordTrace (prefixWord ++ tailWord_160067) baseStart_160067 baseEnd_160067 := by
    simpa [prefixWord, tailWord_160067, baseEnd_160067] using wordTrace_append hprefix tailTrace_160067
  have hstable : (prefixWord ++ tailWord_160067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160067).length < 2 ^ (prefixWord ++ tailWord_160067).sum := by decide
  have hdescent : baseEnd_160067 < baseStart_160067 := by decide
  rcases family_descends (prefixWord ++ tailWord_160067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160084 : List Nat := [2, 4, 1, 1, 2, 3, 7]
def baseStart_160084 : Nat := 118140960795 + 160084 * 2 ^ 59
def prefixEnd_160084 : Nat := 4983230072969 + 3 ^ 40 * 160084 * 2
def baseEnd_160084 : Nat := 8118522182168583142103

theorem tailTrace_160084 : CollatzResearch.WordTrace tailWord_160084 prefixEnd_160084 8118522182168583142103 := by
  unfold tailWord_160084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919371576025241507823653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3892495434700322010431537 2919371576025241507823653)
  ·
    refine ⟨547382170504732782716935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2919371576025241507823653 547382170504732782716935)
    ·
      refine ⟨821073255757099174075403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547382170504732782716935 821073255757099174075403)
      ·
        refine ⟨1231609883635648761113105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 821073255757099174075403 1231609883635648761113105)
        ·
          refine ⟨923707412726736570834829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1231609883635648761113105 923707412726736570834829)
          ·
            refine ⟨346390279772526214063061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923707412726736570834829 346390279772526214063061)
            ·
              refine ⟨8118522182168583142103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 346390279772526214063061 8118522182168583142103)
              ·
                rfl

theorem cell20_160084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_160084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160084 prefixEnd_160084 := by exact prefixLift 160084
  have htrace : WordTrace (prefixWord ++ tailWord_160084) baseStart_160084 baseEnd_160084 := by
    simpa [prefixWord, tailWord_160084, baseEnd_160084] using wordTrace_append hprefix tailTrace_160084
  have hstable : (prefixWord ++ tailWord_160084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160084).length < 2 ^ (prefixWord ++ tailWord_160084).sum := by decide
  have hdescent : baseEnd_160084 < baseStart_160084 := by decide
  rcases family_descends (prefixWord ++ tailWord_160084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160105 : List Nat := [1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_160105 : Nat := 118140960795 + 160105 * 2 ^ 59
def prefixEnd_160105 : Nat := 4983230072969 + 3 ^ 40 * 160105 * 2
def baseEnd_160105 : Nat := 24358761537244836192947

theorem tailTrace_160105 : CollatzResearch.WordTrace tailWord_160105 prefixEnd_160105 24358761537244836192947 := by
  unfold tailWord_160105
  simp only [CollatzResearch.WordTrace]
  refine ⟨5839509084974403602161769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3893006056649602401441179 5839509084974403602161769)
  ·
    refine ⟨4379631813730802701621327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5839509084974403602161769 4379631813730802701621327)
    ·
      refine ⟨6569447720596204052431991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4379631813730802701621327 6569447720596204052431991)
      ·
        refine ⟨9854171580894306078647987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6569447720596204052431991 9854171580894306078647987)
        ·
          refine ⟨14781257371341459117971981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9854171580894306078647987 14781257371341459117971981)
          ·
            refine ⟨5542971514253047169239493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14781257371341459117971981 5542971514253047169239493)
            ·
              refine ⟨1039307158922446344232405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5542971514253047169239493 1039307158922446344232405)
              ·
                refine ⟨24358761537244836192947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1039307158922446344232405 24358761537244836192947)
                ·
                  rfl

theorem cell20_160105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_160105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160105 prefixEnd_160105 := by exact prefixLift 160105
  have htrace : WordTrace (prefixWord ++ tailWord_160105) baseStart_160105 baseEnd_160105 := by
    simpa [prefixWord, tailWord_160105, baseEnd_160105] using wordTrace_append hprefix tailTrace_160105
  have hstable : (prefixWord ++ tailWord_160105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160105).length < 2 ^ (prefixWord ++ tailWord_160105).sum := by decide
  have hdescent : baseEnd_160105 < baseStart_160105 := by decide
  rcases family_descends (prefixWord ++ tailWord_160105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160118 : List Nat := [5, 1, 1, 4, 1, 1, 1, 6]
def baseStart_160118 : Nat := 118140960795 + 160118 * 2 ^ 59
def prefixEnd_160118 : Nat := 4983230072969 + 3 ^ 40 * 160118 * 2
def baseEnd_160118 : Nat := 24360739388654747048485

theorem tailTrace_160118 : CollatzResearch.WordTrace tailWord_160118 prefixEnd_160118 24360739388654747048485 := by
  unfold tailWord_160118
  simp only [CollatzResearch.WordTrace]
  refine ⟨364998952120456676399063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3893322155951537881590005 364998952120456676399063)
  ·
    refine ⟨547498428180685014598595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 364998952120456676399063 547498428180685014598595)
    ·
      refine ⟨821247642271027521897893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547498428180685014598595 821247642271027521897893)
      ·
        refine ⟨153983932925817660355855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 821247642271027521897893 153983932925817660355855)
        ·
          refine ⟨230975899388726490533783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153983932925817660355855 230975899388726490533783)
          ·
            refine ⟨346463849083089735800675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230975899388726490533783 346463849083089735800675)
            ·
              refine ⟨519695773624634603701013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346463849083089735800675 519695773624634603701013)
              ·
                refine ⟨24360739388654747048485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 519695773624634603701013 24360739388654747048485)
                ·
                  rfl

theorem cell20_160118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_160118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160118 prefixEnd_160118 := by exact prefixLift 160118
  have htrace : WordTrace (prefixWord ++ tailWord_160118) baseStart_160118 baseEnd_160118 := by
    simpa [prefixWord, tailWord_160118, baseEnd_160118] using wordTrace_append hprefix tailTrace_160118
  have hstable : (prefixWord ++ tailWord_160118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160118).length < 2 ^ (prefixWord ++ tailWord_160118).sum := by decide
  have hdescent : baseEnd_160118 < baseStart_160118 := by decide
  rcases family_descends (prefixWord ++ tailWord_160118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160160 : List Nat := [2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_160160 : Nat := 118140960795 + 160160 * 2 ^ 59
def prefixEnd_160160 : Nat := 4983230072969 + 3 ^ 40 * 160160 * 2
def baseEnd_160160 : Nat := 24367129370132920581761

theorem tailTrace_160160 : CollatzResearch.WordTrace tailWord_160160 prefixEnd_160160 24367129370132920581761 := by
  unfold tailWord_160160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2920757549887573997706967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3894343399850098663609289 2920757549887573997706967)
  ·
    refine ⟨4381136324831360996560451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2920757549887573997706967 4381136324831360996560451)
    ·
      refine ⟨6571704487247041494840677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4381136324831360996560451 6571704487247041494840677)
      ·
        refine ⟨1232194591358820280282627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6571704487247041494840677 1232194591358820280282627)
        ·
          refine ⟨1848291887038230420423941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232194591358820280282627 1848291887038230420423941)
          ·
            refine ⟨346554728819668203829489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1848291887038230420423941 346554728819668203829489)
            ·
              refine ⟨259916046614751152872117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346554728819668203829489 259916046614751152872117)
              ·
                refine ⟨24367129370132920581761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 259916046614751152872117 24367129370132920581761)
                ·
                  rfl

theorem cell20_160160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_160160 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160160 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160160 prefixEnd_160160 := by exact prefixLift 160160
  have htrace : WordTrace (prefixWord ++ tailWord_160160) baseStart_160160 baseEnd_160160 := by
    simpa [prefixWord, tailWord_160160, baseEnd_160160] using wordTrace_append hprefix tailTrace_160160
  have hstable : (prefixWord ++ tailWord_160160).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160160).length < 2 ^ (prefixWord ++ tailWord_160160).sum := by decide
  have hdescent : baseEnd_160160 < baseStart_160160 := by decide
  rcases family_descends (prefixWord ++ tailWord_160160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160163 : List Nat := [1, 1, 1, 4, 1, 6, 2, 1, 3]
def baseStart_160163 : Nat := 118140960795 + 160163 * 2 ^ 59
def prefixEnd_160163 : Nat := 4983230072969 + 3 ^ 40 * 160163 * 2
def baseEnd_160163 : Nat := 73102757392144084645271

theorem tailTrace_160163 : CollatzResearch.WordTrace tailWord_160163 prefixEnd_160163 73102757392144084645271 := by
  unfold tailWord_160163
  simp only [CollatzResearch.WordTrace]
  refine ⟨5841624518764279507773143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3894416345842853005182095 5841624518764279507773143)
  ·
    refine ⟨8762436778146419261659715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5841624518764279507773143 8762436778146419261659715)
    ·
      refine ⟨13143655167219628892489573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8762436778146419261659715 13143655167219628892489573)
      ·
        refine ⟨2464435343853680417341795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13143655167219628892489573 2464435343853680417341795)
        ·
          refine ⟨3696653015780520626012693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2464435343853680417341795 3696653015780520626012693)
          ·
            refine ⟨173280610114711904344345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3696653015780520626012693 173280610114711904344345)
            ·
              refine ⟨129960457586033928258259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173280610114711904344345 129960457586033928258259)
              ·
                refine ⟨194940686379050892387389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129960457586033928258259 194940686379050892387389)
                ·
                  refine ⟨73102757392144084645271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 194940686379050892387389 73102757392144084645271)
                  ·
                    rfl

theorem cell20_160163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 3].length) (baseStart_160163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160163 prefixEnd_160163 := by exact prefixLift 160163
  have htrace : WordTrace (prefixWord ++ tailWord_160163) baseStart_160163 baseEnd_160163 := by
    simpa [prefixWord, tailWord_160163, baseEnd_160163] using wordTrace_append hprefix tailTrace_160163
  have hstable : (prefixWord ++ tailWord_160163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160163).length < 2 ^ (prefixWord ++ tailWord_160163).sum := by decide
  have hdescent : baseEnd_160163 < baseStart_160163 := by decide
  rcases family_descends (prefixWord ++ tailWord_160163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160198 : List Nat := [6, 1, 13]
def baseStart_160198 : Nat := 118140960795 + 160198 * 2 ^ 59
def prefixEnd_160198 : Nat := 4983230072969 + 3 ^ 40 * 160198 * 2
def baseEnd_160198 : Nat := 100300044370150231109

theorem tailTrace_160198 : CollatzResearch.WordTrace tailWord_160198 prefixEnd_160198 100300044370150231109 := by
  unfold tailWord_160198
  simp only [CollatzResearch.WordTrace]
  refine ⟨182590658551171265165539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3895267382424986990198165 182590658551171265165539)
  ·
    refine ⟨273885987826756897748309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 182590658551171265165539 273885987826756897748309)
    ·
      refine ⟨100300044370150231109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 273885987826756897748309 100300044370150231109)
      ·
        rfl

theorem cell20_160198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 13].length) (baseStart_160198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160198 prefixEnd_160198 := by exact prefixLift 160198
  have htrace : WordTrace (prefixWord ++ tailWord_160198) baseStart_160198 baseEnd_160198 := by
    simpa [prefixWord, tailWord_160198, baseEnd_160198] using wordTrace_append hprefix tailTrace_160198
  have hstable : (prefixWord ++ tailWord_160198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160198).length < 2 ^ (prefixWord ++ tailWord_160198).sum := by decide
  have hdescent : baseEnd_160198 < baseStart_160198 := by decide
  rcases family_descends (prefixWord ++ tailWord_160198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160204 : List Nat := [2, 2, 1, 4, 3, 2, 2, 2, 2]
def baseStart_160204 : Nat := 118140960795 + 160204 * 2 ^ 59
def prefixEnd_160204 : Nat := 4983230072969 + 3 ^ 40 * 160204 * 2
def baseEnd_160204 : Nat := 73121470909330164278437

theorem tailTrace_160204 : CollatzResearch.WordTrace tailWord_160204 prefixEnd_160204 73121470909330164278437 := by
  unfold tailWord_160204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921559955807871755007833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3895413274410495673343777 2921559955807871755007833)
  ·
    refine ⟨2191169966855903816255875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2921559955807871755007833 2191169966855903816255875)
    ·
      refine ⟨3286754950283855724383813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191169966855903816255875 3286754950283855724383813)
      ·
        refine ⟨616266553178222948321965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3286754950283855724383813 616266553178222948321965)
        ·
          refine ⟨231099957441833605620737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616266553178222948321965 231099957441833605620737)
          ·
            refine ⟨173324968081375204215553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231099957441833605620737 173324968081375204215553)
            ·
              refine ⟨129993726061031403161665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173324968081375204215553 129993726061031403161665)
              ·
                refine ⟨97495294545773552371249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129993726061031403161665 97495294545773552371249)
                ·
                  refine ⟨73121470909330164278437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97495294545773552371249 73121470909330164278437)
                  ·
                    rfl

theorem cell20_160204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_160204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160204 prefixEnd_160204 := by exact prefixLift 160204
  have htrace : WordTrace (prefixWord ++ tailWord_160204) baseStart_160204 baseEnd_160204 := by
    simpa [prefixWord, tailWord_160204, baseEnd_160204] using wordTrace_append hprefix tailTrace_160204
  have hstable : (prefixWord ++ tailWord_160204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160204).length < 2 ^ (prefixWord ++ tailWord_160204).sum := by decide
  have hdescent : baseEnd_160204 < baseStart_160204 := by decide
  rcases family_descends (prefixWord ++ tailWord_160204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160236 : List Nat := [2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_160236 : Nat := 118140960795 + 160236 * 2 ^ 59
def prefixEnd_160236 : Nat := 4983230072969 + 3 ^ 40 * 160236 * 2
def baseEnd_160236 : Nat := 24378692193760091737213

theorem tailTrace_160236 : CollatzResearch.WordTrace tailWord_160236 prefixEnd_160236 24378692193760091737213 := by
  unfold tailWord_160236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922143523749906487590281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3896191364999875316787041 2922143523749906487590281)
  ·
    refine ⟨2191607642812429865692711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2922143523749906487590281 2191607642812429865692711)
    ·
      refine ⟨3287411464218644798539067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191607642812429865692711 3287411464218644798539067)
      ·
        refine ⟨4931117196327967197808601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3287411464218644798539067 4931117196327967197808601)
        ·
          refine ⟨3698337897245975398356451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4931117196327967197808601 3698337897245975398356451)
          ·
            refine ⟨5547506845868963097534677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3698337897245975398356451 5547506845868963097534677)
            ·
              refine ⟨130019691700053822598469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5547506845868963097534677 130019691700053822598469)
              ·
                refine ⟨24378692193760091737213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130019691700053822598469 24378692193760091737213)
                ·
                  rfl

theorem cell20_160236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_160236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160236 prefixEnd_160236 := by exact prefixLift 160236
  have htrace : WordTrace (prefixWord ++ tailWord_160236) baseStart_160236 baseEnd_160236 := by
    simpa [prefixWord, tailWord_160236, baseEnd_160236] using wordTrace_append hprefix tailTrace_160236
  have hstable : (prefixWord ++ tailWord_160236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160236).length < 2 ^ (prefixWord ++ tailWord_160236).sum := by decide
  have hdescent : baseEnd_160236 < baseStart_160236 := by decide
  rcases family_descends (prefixWord ++ tailWord_160236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160260 : List Nat := [2, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_160260 : Nat := 118140960795 + 160260 * 2 ^ 59
def prefixEnd_160260 : Nat := 4983230072969 + 3 ^ 40 * 160260 * 2
def baseEnd_160260 : Nat := 73147030835242858411541

theorem tailTrace_160260 : CollatzResearch.WordTrace tailWord_160260 prefixEnd_160260 73147030835242858411541 := by
  unfold tailWord_160260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922581199706432537027117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3896774932941910049369489 2922581199706432537027117)
  ·
    refine ⟨1095967949889912201385169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2922581199706432537027117 1095967949889912201385169)
    ·
      refine ⟨821975962417434151038877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1095967949889912201385169 821975962417434151038877)
      ·
        refine ⟨308240985906537806639579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 821975962417434151038877 308240985906537806639579)
        ·
          refine ⟨462361478859806709959369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308240985906537806639579 462361478859806709959369)
          ·
            refine ⟨346771109144855032469527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462361478859806709959369 346771109144855032469527)
            ·
              refine ⟨520156663717282548704291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346771109144855032469527 520156663717282548704291)
              ·
                refine ⟨780234995575923823056437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 520156663717282548704291 780234995575923823056437)
                ·
                  refine ⟨73147030835242858411541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 780234995575923823056437 73147030835242858411541)
                  ·
                    rfl

theorem cell20_160260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_160260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160260 prefixEnd_160260 := by exact prefixLift 160260
  have htrace : WordTrace (prefixWord ++ tailWord_160260) baseStart_160260 baseEnd_160260 := by
    simpa [prefixWord, tailWord_160260, baseEnd_160260] using wordTrace_append hprefix tailTrace_160260
  have hstable : (prefixWord ++ tailWord_160260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160260).length < 2 ^ (prefixWord ++ tailWord_160260).sum := by decide
  have hdescent : baseEnd_160260 < baseStart_160260 := by decide
  rcases family_descends (prefixWord ++ tailWord_160260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160267 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_160267 : Nat := 118140960795 + 160267 * 2 ^ 59
def prefixEnd_160267 : Nat := 4983230072969 + 3 ^ 40 * 160267 * 2
def baseEnd_160267 : Nat := 73150225825981945178179

theorem tailTrace_160267 : CollatzResearch.WordTrace tailWord_160267 prefixEnd_160267 73150225825981945178179 := by
  unfold tailWord_160267
  simp only [CollatzResearch.WordTrace]
  refine ⟨5845417710387505269559055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3896945140258336846372703 5845417710387505269559055)
  ·
    refine ⟨8768126565581257904338583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5845417710387505269559055 8768126565581257904338583)
    ·
      refine ⟨13152189848371886856507875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8768126565581257904338583 13152189848371886856507875)
      ·
        refine ⟨19728284772557830284761813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13152189848371886856507875 19728284772557830284761813)
        ·
          refine ⟨462381674356824147299105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 19728284772557830284761813 462381674356824147299105)
          ·
            refine ⟨346786255767618110474329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 462381674356824147299105 346786255767618110474329)
            ·
              refine ⟨260089691825713582855747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346786255767618110474329 260089691825713582855747)
              ·
                refine ⟨390134537738570374283621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260089691825713582855747 390134537738570374283621)
                ·
                  refine ⟨73150225825981945178179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390134537738570374283621 73150225825981945178179)
                  ·
                    rfl

theorem cell20_160267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_160267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160267 prefixEnd_160267 := by exact prefixLift 160267
  have htrace : WordTrace (prefixWord ++ tailWord_160267) baseStart_160267 baseEnd_160267 := by
    simpa [prefixWord, tailWord_160267, baseEnd_160267] using wordTrace_append hprefix tailTrace_160267
  have hstable : (prefixWord ++ tailWord_160267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160267).length < 2 ^ (prefixWord ++ tailWord_160267).sum := by decide
  have hdescent : baseEnd_160267 < baseStart_160267 := by decide
  rcases family_descends (prefixWord ++ tailWord_160267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160291 : List Nat := [1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_160291 : Nat := 118140960795 + 160291 * 2 ^ 59
def prefixEnd_160291 : Nat := 4983230072969 + 3 ^ 40 * 160291 * 2
def baseEnd_160291 : Nat := 24387060026648176126027

theorem tailTrace_160291 : CollatzResearch.WordTrace tailWord_160291 prefixEnd_160291 24387060026648176126027 := by
  unfold tailWord_160291
  simp only [CollatzResearch.WordTrace]
  refine ⟨5846293062300557368432727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3897528708200371578955151 5846293062300557368432727)
  ·
    refine ⟨8769439593450836052649091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5846293062300557368432727 8769439593450836052649091)
    ·
      refine ⟨13154159390176254078973637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8769439593450836052649091 13154159390176254078973637)
      ·
        refine ⟨2466404885658047639807557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13154159390176254078973637 2466404885658047639807557)
        ·
          refine ⟨462450916060883932463917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2466404885658047639807557 462450916060883932463917)
          ·
            refine ⟨173419093522831474673969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 462450916060883932463917 173419093522831474673969)
            ·
              refine ⟨130064320142123606005477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173419093522831474673969 130064320142123606005477)
              ·
                refine ⟨24387060026648176126027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130064320142123606005477 24387060026648176126027)
                ·
                  rfl

theorem cell20_160291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_160291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160291 prefixEnd_160291 := by exact prefixLift 160291
  have htrace : WordTrace (prefixWord ++ tailWord_160291) baseStart_160291 baseEnd_160291 := by
    simpa [prefixWord, tailWord_160291, baseEnd_160291] using wordTrace_append hprefix tailTrace_160291
  have hstable : (prefixWord ++ tailWord_160291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160291).length < 2 ^ (prefixWord ++ tailWord_160291).sum := by decide
  have hdescent : baseEnd_160291 < baseStart_160291 := by decide
  rcases family_descends (prefixWord ++ tailWord_160291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160308 : List Nat := [2, 5, 1, 3, 1, 2, 6]
def baseStart_160308 : Nat := 118140960795 + 160308 * 2 ^ 59
def prefixEnd_160308 : Nat := 4983230072969 + 3 ^ 40 * 160308 * 2
def baseEnd_160308 : Nat := 8129882149240891645705

theorem tailTrace_160308 : CollatzResearch.WordTrace tailWord_160308 prefixEnd_160308 8129882149240891645705 := by
  unfold tailWord_160308
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923456551619484635900789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3897942068825979514534385 2923456551619484635900789)
  ·
    refine ⟨274074051714326684615699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2923456551619484635900789 274074051714326684615699)
    ·
      refine ⟨411111077571490026923549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274074051714326684615699 411111077571490026923549)
      ·
        refine ⟨154166654089308760096331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411111077571490026923549 154166654089308760096331)
        ·
          refine ⟨231249981133963140144497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154166654089308760096331 231249981133963140144497)
          ·
            refine ⟨173437485850472355108373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231249981133963140144497 173437485850472355108373)
            ·
              refine ⟨8129882149240891645705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173437485850472355108373 8129882149240891645705)
              ·
                rfl

theorem cell20_160308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_160308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160308 prefixEnd_160308 := by exact prefixLift 160308
  have htrace : WordTrace (prefixWord ++ tailWord_160308) baseStart_160308 baseEnd_160308 := by
    simpa [prefixWord, tailWord_160308, baseEnd_160308] using wordTrace_append hprefix tailTrace_160308
  have hstable : (prefixWord ++ tailWord_160308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160308).length < 2 ^ (prefixWord ++ tailWord_160308).sum := by decide
  have hdescent : baseEnd_160308 < baseStart_160308 := by decide
  rcases family_descends (prefixWord ++ tailWord_160308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160318 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_160318 : Nat := 118140960795 + 160318 * 2 ^ 59
def prefixEnd_160318 : Nat := 4983230072969 + 3 ^ 40 * 160318 * 2
def baseEnd_160318 : Nat := 73173503615652434477971

theorem tailTrace_160318 : CollatzResearch.WordTrace tailWord_160318 prefixEnd_160318 73173503615652434477971 := by
  unfold tailWord_160318
  simp only [CollatzResearch.WordTrace]
  refine ⟨730909729150342622458201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3898185222135160653110405 730909729150342622458201)
  ·
    refine ⟨548182296862756966843651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 730909729150342622458201 548182296862756966843651)
    ·
      refine ⟨822273445294135450265477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548182296862756966843651 822273445294135450265477)
      ·
        refine ⟨154176270992650396924777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 822273445294135450265477 154176270992650396924777)
        ·
          refine ⟨115632203244487797693583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154176270992650396924777 115632203244487797693583)
          ·
            refine ⟨173448304866731696540375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115632203244487797693583 173448304866731696540375)
            ·
              refine ⟨260172457300097544810563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173448304866731696540375 260172457300097544810563)
              ·
                refine ⟨390258685950146317215845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260172457300097544810563 390258685950146317215845)
                ·
                  refine ⟨73173503615652434477971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390258685950146317215845 73173503615652434477971)
                  ·
                    rfl

theorem cell20_160318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_160318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160318 prefixEnd_160318 := by exact prefixLift 160318
  have htrace : WordTrace (prefixWord ++ tailWord_160318) baseStart_160318 baseEnd_160318 := by
    simpa [prefixWord, tailWord_160318, baseEnd_160318] using wordTrace_append hprefix tailTrace_160318
  have hstable : (prefixWord ++ tailWord_160318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160318).length < 2 ^ (prefixWord ++ tailWord_160318).sum := by decide
  have hdescent : baseEnd_160318 < baseStart_160318 := by decide
  rcases family_descends (prefixWord ++ tailWord_160318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160319 : List Nat := [1, 1, 2, 2, 3, 2, 2, 4, 3]
def baseStart_160319 : Nat := 118140960795 + 160319 * 2 ^ 59
def prefixEnd_160319 : Nat := 4983230072969 + 3 ^ 40 * 160319 * 2
def baseEnd_160319 : Nat := 73173960042900875444633

theorem tailTrace_160319 : CollatzResearch.WordTrace tailWord_160319 prefixEnd_160319 73173960042900875444633 := by
  unfold tailWord_160319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5847314306199118150452011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3898209537466078766968007 5847314306199118150452011)
  ·
    refine ⟨8770971459298677225678017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5847314306199118150452011 8770971459298677225678017)
    ·
      refine ⟨6578228594474007919258513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8770971459298677225678017 6578228594474007919258513)
      ·
        refine ⟨4933671445855505939443885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6578228594474007919258513 4933671445855505939443885)
        ·
          refine ⟨1850126792195814727291457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4933671445855505939443885 1850126792195814727291457)
          ·
            refine ⟨1387595094146861045468593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1850126792195814727291457 1387595094146861045468593)
            ·
              refine ⟨1040696320610145784101445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1387595094146861045468593 1040696320610145784101445)
              ·
                refine ⟨195130560114402334519021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1040696320610145784101445 195130560114402334519021)
                ·
                  refine ⟨73173960042900875444633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195130560114402334519021 73173960042900875444633)
                  ·
                    rfl

theorem cell20_160319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_160319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160319 prefixEnd_160319 := by exact prefixLift 160319
  have htrace : WordTrace (prefixWord ++ tailWord_160319) baseStart_160319 baseEnd_160319 := by
    simpa [prefixWord, tailWord_160319, baseEnd_160319] using wordTrace_append hprefix tailTrace_160319
  have hstable : (prefixWord ++ tailWord_160319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160319).length < 2 ^ (prefixWord ++ tailWord_160319).sum := by decide
  have hdescent : baseEnd_160319 < baseStart_160319 := by decide
  rcases family_descends (prefixWord ++ tailWord_160319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160373 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 2]
def baseStart_160373 : Nat := 118140960795 + 160373 * 2 ^ 59
def prefixEnd_160373 : Nat := 4983230072969 + 3 ^ 40 * 160373 * 2
def baseEnd_160373 : Nat := 73198607114316687644413

theorem tailTrace_160373 : CollatzResearch.WordTrace tailWord_160373 prefixEnd_160373 73198607114316687644413 := by
  unfold tailWord_160373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849283848003485372917773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3899522565335656915278515 5849283848003485372917773)
  ·
    refine ⟨2193481443001307014844165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5849283848003485372917773 2193481443001307014844165)
    ·
      refine ⟨411277770562745065283281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2193481443001307014844165 411277770562745065283281)
      ·
        refine ⟨308458327922058798962461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411277770562745065283281 308458327922058798962461)
        ·
          refine ⟨115671872970772049610923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308458327922058798962461 115671872970772049610923)
          ·
            refine ⟨173507809456158074416385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115671872970772049610923 173507809456158074416385)
            ·
              refine ⟨130130857092118555812289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173507809456158074416385 130130857092118555812289)
              ·
                refine ⟨97598142819088916859217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130130857092118555812289 97598142819088916859217)
                ·
                  refine ⟨73198607114316687644413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97598142819088916859217 73198607114316687644413)
                  ·
                    rfl

theorem cell20_160373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_160373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160373 prefixEnd_160373 := by exact prefixLift 160373
  have htrace : WordTrace (prefixWord ++ tailWord_160373) baseStart_160373 baseEnd_160373 := by
    simpa [prefixWord, tailWord_160373, baseEnd_160373] using wordTrace_append hprefix tailTrace_160373
  have hstable : (prefixWord ++ tailWord_160373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160373).length < 2 ^ (prefixWord ++ tailWord_160373).sum := by decide
  have hdescent : baseEnd_160373 < baseStart_160373 := by decide
  rcases family_descends (prefixWord ++ tailWord_160373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160377 : List Nat := [1, 2, 1, 3, 3, 4, 2, 2, 2]
def baseStart_160377 : Nat := 118140960795 + 160377 * 2 ^ 59
def prefixEnd_160377 : Nat := 4983230072969 + 3 ^ 40 * 160377 * 2
def baseEnd_160377 : Nat := 73200432823310451511063

theorem tailTrace_160377 : CollatzResearch.WordTrace tailWord_160377 prefixEnd_160377 73200432823310451511063 := by
  unfold tailWord_160377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5849429739988994056063385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3899619826659329370708923 5849429739988994056063385)
  ·
    refine ⟨4387072304991745542047539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5849429739988994056063385 4387072304991745542047539)
    ·
      refine ⟨6580608457487618313071309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4387072304991745542047539 6580608457487618313071309)
      ·
        refine ⟨2467728171557856867401741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6580608457487618313071309 2467728171557856867401741)
        ·
          refine ⟨925398064334196325275653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2467728171557856867401741 925398064334196325275653)
          ·
            refine ⟨173512137062661810989185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 925398064334196325275653 173512137062661810989185)
            ·
              refine ⟨130134102796996358241889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173512137062661810989185 130134102796996358241889)
              ·
                refine ⟨97600577097747268681417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130134102796996358241889 97600577097747268681417)
                ·
                  refine ⟨73200432823310451511063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97600577097747268681417 73200432823310451511063)
                  ·
                    rfl

theorem cell20_160377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_160377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160377 prefixEnd_160377 := by exact prefixLift 160377
  have htrace : WordTrace (prefixWord ++ tailWord_160377) baseStart_160377 baseEnd_160377 := by
    simpa [prefixWord, tailWord_160377, baseEnd_160377] using wordTrace_append hprefix tailTrace_160377
  have hstable : (prefixWord ++ tailWord_160377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160377).length < 2 ^ (prefixWord ++ tailWord_160377).sum := by decide
  have hdescent : baseEnd_160377 < baseStart_160377 := by decide
  rcases family_descends (prefixWord ++ tailWord_160377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160378 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_160378 : Nat := 118140960795 + 160378 * 2 ^ 59
def prefixEnd_160378 : Nat := 4983230072969 + 3 ^ 40 * 160378 * 2
def baseEnd_160378 : Nat := 73200889250558892477725

theorem tailTrace_160378 : CollatzResearch.WordTrace tailWord_160378 prefixEnd_160378 73200889250558892477725 := by
  unfold tailWord_160378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462366553246342806712447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3899644141990247484566525 1462366553246342806712447)
  ·
    refine ⟨2193549829869514210068671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1462366553246342806712447 2193549829869514210068671)
    ·
      refine ⟨3290324744804271315103007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2193549829869514210068671 3290324744804271315103007)
      ·
        refine ⟨4935487117206406972654511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3290324744804271315103007 4935487117206406972654511)
        ·
          refine ⟨7403230675809610458981767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4935487117206406972654511 7403230675809610458981767)
          ·
            refine ⟨11104846013714415688472651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7403230675809610458981767 11104846013714415688472651)
            ·
              refine ⟨16657269020571623532708977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11104846013714415688472651 16657269020571623532708977)
              ·
                refine ⟨12492951765428717649531733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16657269020571623532708977 12492951765428717649531733)
                ·
                  refine ⟨73200889250558892477725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12492951765428717649531733 73200889250558892477725)
                  ·
                    rfl

theorem cell20_160378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_160378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160378 prefixEnd_160378 := by exact prefixLift 160378
  have htrace : WordTrace (prefixWord ++ tailWord_160378) baseStart_160378 baseEnd_160378 := by
    simpa [prefixWord, tailWord_160378, baseEnd_160378] using wordTrace_append hprefix tailTrace_160378
  have hstable : (prefixWord ++ tailWord_160378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160378).length < 2 ^ (prefixWord ++ tailWord_160378).sum := by decide
  have hdescent : baseEnd_160378 < baseStart_160378 := by decide
  rcases family_descends (prefixWord ++ tailWord_160378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160388 : List Nat := [2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_160388 : Nat := 118140960795 + 160388 * 2 ^ 59
def prefixEnd_160388 : Nat := 4983230072969 + 3 ^ 40 * 160388 * 2
def baseEnd_160388 : Nat := 24401817841014434048117

theorem tailTrace_160388 : CollatzResearch.WordTrace tailWord_160388 prefixEnd_160388 24401817841014434048117 := by
  unfold tailWord_160388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924915471474571467356909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3899887295299428623142545 2924915471474571467356909)
  ·
    refine ⟨1096843301802964300258841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2924915471474571467356909 1096843301802964300258841)
    ·
      refine ⟨822632476352223225194131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1096843301802964300258841 822632476352223225194131)
      ·
        refine ⟨1233948714528334837791197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822632476352223225194131 1233948714528334837791197)
        ·
          refine ⟨462730767948125564171699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1233948714528334837791197 462730767948125564171699)
          ·
            refine ⟨694096151922188346257549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462730767948125564171699 694096151922188346257549)
            ·
              refine ⟨260286056970820629846581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694096151922188346257549 260286056970820629846581)
              ·
                refine ⟨24401817841014434048117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260286056970820629846581 24401817841014434048117)
                ·
                  rfl

theorem cell20_160388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_160388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160388 prefixEnd_160388 := by exact prefixLift 160388
  have htrace : WordTrace (prefixWord ++ tailWord_160388) baseStart_160388 baseEnd_160388 := by
    simpa [prefixWord, tailWord_160388, baseEnd_160388] using wordTrace_append hprefix tailTrace_160388
  have hstable : (prefixWord ++ tailWord_160388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160388).length < 2 ^ (prefixWord ++ tailWord_160388).sum := by decide
  have hdescent : baseEnd_160388 < baseStart_160388 := by decide
  rcases family_descends (prefixWord ++ tailWord_160388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160429 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_160429 : Nat := 118140960795 + 160429 * 2 ^ 59
def prefixEnd_160429 : Nat := 4983230072969 + 3 ^ 40 * 160429 * 2
def baseEnd_160429 : Nat := 73224167040229381777517

theorem tailTrace_160429 : CollatzResearch.WordTrace tailWord_160429 prefixEnd_160429 73224167040229381777517 := by
  unfold tailWord_160429
  simp only [CollatzResearch.WordTrace]
  refine ⟨5851326335800606936956341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3900884223867071291304227 5851326335800606936956341)
  ·
    refine ⟨548561843981306900339657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5851326335800606936956341 548561843981306900339657)
    ·
      refine ⟨411421382985980175254743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 548561843981306900339657 411421382985980175254743)
      ·
        refine ⟨617132074478970262882115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411421382985980175254743 617132074478970262882115)
        ·
          refine ⟨925698111718455394323173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617132074478970262882115 925698111718455394323173)
          ·
            refine ⟨173568395947210386435595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 925698111718455394323173 173568395947210386435595)
            ·
              refine ⟨260352593920815579653393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173568395947210386435595 260352593920815579653393)
              ·
                refine ⟨195264445440611684740045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260352593920815579653393 195264445440611684740045)
                ·
                  refine ⟨73224167040229381777517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195264445440611684740045 73224167040229381777517)
                  ·
                    rfl

theorem cell20_160429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_160429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160429 prefixEnd_160429 := by exact prefixLift 160429
  have htrace : WordTrace (prefixWord ++ tailWord_160429) baseStart_160429 baseEnd_160429 := by
    simpa [prefixWord, tailWord_160429, baseEnd_160429] using wordTrace_append hprefix tailTrace_160429
  have hstable : (prefixWord ++ tailWord_160429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160429).length < 2 ^ (prefixWord ++ tailWord_160429).sum := by decide
  have hdescent : baseEnd_160429 < baseStart_160429 := by decide
  rcases family_descends (prefixWord ++ tailWord_160429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160485 : List Nat := [1, 3, 1, 4, 1, 2, 8]
def baseStart_160485 : Nat := 118140960795 + 160485 * 2 ^ 59
def prefixEnd_160485 : Nat := 4983230072969 + 3 ^ 40 * 160485 * 2
def baseEnd_160485 : Nat := 8138858551793563990069

theorem tailTrace_160485 : CollatzResearch.WordTrace tailWord_160485 prefixEnd_160485 8138858551793563990069 := by
  unfold tailWord_160485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853368823597728500994909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3902245882398485667329939 5853368823597728500994909)
  ·
    refine ⟨2195013308849148187873091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5853368823597728500994909 2195013308849148187873091)
    ·
      refine ⟨3292519963273722281809637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2195013308849148187873091 3292519963273722281809637)
      ·
        refine ⟨617347493113822927839307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3292519963273722281809637 617347493113822927839307)
        ·
          refine ⟨926021239670734391758961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617347493113822927839307 926021239670734391758961)
          ·
            refine ⟨694515929753050793819221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926021239670734391758961 694515929753050793819221)
            ·
              refine ⟨8138858551793563990069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 694515929753050793819221 8138858551793563990069)
              ·
                rfl

theorem cell20_160485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 8].length) (baseStart_160485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160485 prefixEnd_160485 := by exact prefixLift 160485
  have htrace : WordTrace (prefixWord ++ tailWord_160485) baseStart_160485 baseEnd_160485 := by
    simpa [prefixWord, tailWord_160485, baseEnd_160485] using wordTrace_append hprefix tailTrace_160485
  have hstable : (prefixWord ++ tailWord_160485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160485).length < 2 ^ (prefixWord ++ tailWord_160485).sum := by decide
  have hdescent : baseEnd_160485 < baseStart_160485 := by decide
  rcases family_descends (prefixWord ++ tailWord_160485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160495 : List Nat := [1, 1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_160495 : Nat := 118140960795 + 160495 * 2 ^ 59
def prefixEnd_160495 : Nat := 4983230072969 + 3 ^ 40 * 160495 * 2
def baseEnd_160495 : Nat := 73254291238626485577247

theorem tailTrace_160495 : CollatzResearch.WordTrace tailWord_160495 prefixEnd_160495 73254291238626485577247 := by
  unfold tailWord_160495
  simp only [CollatzResearch.WordTrace]
  refine ⟨5853733553561500208858939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3902489035707666805905959 5853733553561500208858939)
  ·
    refine ⟨8780600330342250313288409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5853733553561500208858939 8780600330342250313288409)
    ·
      refine ⟨6585450247756687734966307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8780600330342250313288409 6585450247756687734966307)
      ·
        refine ⟨9878175371635031602449461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6585450247756687734966307 9878175371635031602449461)
        ·
          refine ⟨926078941090784212729637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9878175371635031602449461 926078941090784212729637)
          ·
            refine ⟨173639801454522039886807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 926078941090784212729637 173639801454522039886807)
            ·
              refine ⟨260459702181783059830211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173639801454522039886807 260459702181783059830211)
              ·
                refine ⟨390689553272674589745317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260459702181783059830211 390689553272674589745317)
                ·
                  refine ⟨73254291238626485577247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 390689553272674589745317 73254291238626485577247)
                  ·
                    rfl

theorem cell20_160495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_160495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160495 prefixEnd_160495 := by exact prefixLift 160495
  have htrace : WordTrace (prefixWord ++ tailWord_160495) baseStart_160495 baseEnd_160495 := by
    simpa [prefixWord, tailWord_160495, baseEnd_160495] using wordTrace_append hprefix tailTrace_160495
  have hstable : (prefixWord ++ tailWord_160495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160495).length < 2 ^ (prefixWord ++ tailWord_160495).sum := by decide
  have hdescent : baseEnd_160495 < baseStart_160495 := by decide
  rcases family_descends (prefixWord ++ tailWord_160495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160502 : List Nat := [5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_160502 : Nat := 118140960795 + 160502 * 2 ^ 59
def prefixEnd_160502 : Nat := 4983230072969 + 3 ^ 40 * 160502 * 2
def baseEnd_160502 : Nat := 24419162076455190781295

theorem tailTrace_160502 : CollatzResearch.WordTrace tailWord_160502 prefixEnd_160502 24419162076455190781295 := by
  unfold tailWord_160502
  simp only [CollatzResearch.WordTrace]
  refine ⟨365874304033508775272735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3902659243024093602909173 365874304033508775272735)
  ·
    refine ⟨548811456050263162909103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 365874304033508775272735 548811456050263162909103)
    ·
      refine ⟨823217184075394744363655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548811456050263162909103 823217184075394744363655)
      ·
        refine ⟨1234825776113092116545483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823217184075394744363655 1234825776113092116545483)
        ·
          refine ⟨1852238664169638174818225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234825776113092116545483 1852238664169638174818225)
          ·
            refine ⟨1389178998127228631113669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852238664169638174818225 1389178998127228631113669)
            ·
              refine ⟨260471062148855368333813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1389178998127228631113669 260471062148855368333813)
              ·
                refine ⟨24419162076455190781295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260471062148855368333813 24419162076455190781295)
                ·
                  rfl

theorem cell20_160502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_160502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160502 prefixEnd_160502 := by exact prefixLift 160502
  have htrace : WordTrace (prefixWord ++ tailWord_160502) baseStart_160502 baseEnd_160502 := by
    simpa [prefixWord, tailWord_160502, baseEnd_160502] using wordTrace_append hprefix tailTrace_160502
  have hstable : (prefixWord ++ tailWord_160502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160502).length < 2 ^ (prefixWord ++ tailWord_160502).sum := by decide
  have hdescent : baseEnd_160502 < baseStart_160502 := by decide
  rcases family_descends (prefixWord ++ tailWord_160502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160509 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 3]
def baseStart_160509 : Nat := 118140960795 + 160509 * 2 ^ 59
def prefixEnd_160509 : Nat := 4983230072969 + 3 ^ 40 * 160509 * 2
def baseEnd_160509 : Nat := 73260681220104659110523

theorem tailTrace_160509 : CollatzResearch.WordTrace tailWord_160509 prefixEnd_160509 73260681220104659110523 := by
  unfold tailWord_160509
  simp only [CollatzResearch.WordTrace]
  refine ⟨5854244175510780599868581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3902829450340520399912387 5854244175510780599868581)
  ·
    refine ⟨1097670782908271362475359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5854244175510780599868581 1097670782908271362475359)
    ·
      refine ⟨1646506174362407043713039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1097670782908271362475359 1646506174362407043713039)
      ·
        refine ⟨2469759261543610565569559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646506174362407043713039 2469759261543610565569559)
        ·
          refine ⟨3704638892315415848354339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2469759261543610565569559 3704638892315415848354339)
          ·
            refine ⟨5556958338473123772531509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3704638892315415848354339 5556958338473123772531509)
            ·
              refine ⟨520964844231855353674829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5556958338473123772531509 520964844231855353674829)
              ·
                refine ⟨195361816586945757628061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 520964844231855353674829 195361816586945757628061)
                ·
                  refine ⟨73260681220104659110523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195361816586945757628061 73260681220104659110523)
                  ·
                    rfl

theorem cell20_160509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_160509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160509 prefixEnd_160509 := by exact prefixLift 160509
  have htrace : WordTrace (prefixWord ++ tailWord_160509) baseStart_160509 baseEnd_160509 := by
    simpa [prefixWord, tailWord_160509, baseEnd_160509] using wordTrace_append hprefix tailTrace_160509
  have hstable : (prefixWord ++ tailWord_160509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160509).length < 2 ^ (prefixWord ++ tailWord_160509).sum := by decide
  have hdescent : baseEnd_160509 < baseStart_160509 := by decide
  rcases family_descends (prefixWord ++ tailWord_160509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160516 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_160516 : Nat := 118140960795 + 160516 * 2 ^ 59
def prefixEnd_160516 : Nat := 4983230072969 + 3 ^ 40 * 160516 * 2
def baseEnd_160516 : Nat := 73263876210843745877161

theorem tailTrace_160516 : CollatzResearch.WordTrace tailWord_160516 prefixEnd_160516 73263876210843745877161 := by
  unfold tailWord_160516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927249743242710397686701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3902999657656947196915601 2927249743242710397686701)
  ·
    refine ⟨1097718653716016399132513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2927249743242710397686701 1097718653716016399132513)
    ·
      refine ⟨823288990287012299349385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1097718653716016399132513 823288990287012299349385)
      ·
        refine ⟨617466742715259224512039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 823288990287012299349385 617466742715259224512039)
        ·
          refine ⟨926200114072888836768059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617466742715259224512039 926200114072888836768059)
          ·
            refine ⟨1389300171109333255152089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 926200114072888836768059 1389300171109333255152089)
            ·
              refine ⟨1041975128331999941364067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389300171109333255152089 1041975128331999941364067)
              ·
                refine ⟨1562962692497999912046101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1041975128331999941364067 1562962692497999912046101)
                ·
                  refine ⟨73263876210843745877161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1562962692497999912046101 73263876210843745877161)
                  ·
                    rfl

theorem cell20_160516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_160516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160516 prefixEnd_160516 := by exact prefixLift 160516
  have htrace : WordTrace (prefixWord ++ tailWord_160516) baseStart_160516 baseEnd_160516 := by
    simpa [prefixWord, tailWord_160516, baseEnd_160516] using wordTrace_append hprefix tailTrace_160516
  have hstable : (prefixWord ++ tailWord_160516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160516).length < 2 ^ (prefixWord ++ tailWord_160516).sum := by decide
  have hdescent : baseEnd_160516 < baseStart_160516 := by decide
  rcases family_descends (prefixWord ++ tailWord_160516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160533 : List Nat := [1, 3, 2, 1, 2, 2, 2, 5, 2]
def baseStart_160533 : Nat := 118140960795 + 160533 * 2 ^ 59
def prefixEnd_160533 : Nat := 4983230072969 + 3 ^ 40 * 160533 * 2
def baseEnd_160533 : Nat := 73271635474067242310425

theorem tailTrace_160533 : CollatzResearch.WordTrace tailWord_160533 prefixEnd_160533 73271635474067242310425 := by
  unfold tailWord_160533
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855119527423832698742253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3903413018282555132494835 5855119527423832698742253)
  ·
    refine ⟨2195669822783937262028345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5855119527423832698742253 2195669822783937262028345)
    ·
      refine ⟨1646752367087952946521259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2195669822783937262028345 1646752367087952946521259)
      ·
        refine ⟨2470128550631929419781889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1646752367087952946521259 2470128550631929419781889)
        ·
          refine ⟨1852596412973947064836417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2470128550631929419781889 1852596412973947064836417)
          ·
            refine ⟨1389447309730460298627313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1852596412973947064836417 1389447309730460298627313)
            ·
              refine ⟨1042085482297845223970485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1389447309730460298627313 1042085482297845223970485)
              ·
                refine ⟨97695513965422989747233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1042085482297845223970485 97695513965422989747233)
                ·
                  refine ⟨73271635474067242310425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97695513965422989747233 73271635474067242310425)
                  ·
                    rfl

theorem cell20_160533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_160533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160533 prefixEnd_160533 := by exact prefixLift 160533
  have htrace : WordTrace (prefixWord ++ tailWord_160533) baseStart_160533 baseEnd_160533 := by
    simpa [prefixWord, tailWord_160533, baseEnd_160533] using wordTrace_append hprefix tailTrace_160533
  have hstable : (prefixWord ++ tailWord_160533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160533).length < 2 ^ (prefixWord ++ tailWord_160533).sum := by decide
  have hdescent : baseEnd_160533 < baseStart_160533 := by decide
  rcases family_descends (prefixWord ++ tailWord_160533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160537 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_160537 : Nat := 118140960795 + 160537 * 2 ^ 59
def prefixEnd_160537 : Nat := 4983230072969 + 3 ^ 40 * 160537 * 2
def baseEnd_160537 : Nat := 73273461183061006177075

theorem tailTrace_160537 : CollatzResearch.WordTrace tailWord_160537 prefixEnd_160537 73273461183061006177075 := by
  unfold tailWord_160537
  simp only [CollatzResearch.WordTrace]
  refine ⟨5855265419409341381887865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3903510279606227587925243 5855265419409341381887865)
  ·
    refine ⟨4391449064557006036415899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5855265419409341381887865 4391449064557006036415899)
    ·
      refine ⟨6587173596835509054623849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391449064557006036415899 6587173596835509054623849)
      ·
        refine ⟨4940380197626631790967887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6587173596835509054623849 4940380197626631790967887)
        ·
          refine ⟨7410570296439947686451831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4940380197626631790967887 7410570296439947686451831)
          ·
            refine ⟨11115855444659921529677747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7410570296439947686451831 11115855444659921529677747)
            ·
              refine ⟨16673783166989882294516621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11115855444659921529677747 16673783166989882294516621)
              ·
                refine ⟨6252668687621205860443733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16673783166989882294516621 6252668687621205860443733)
                ·
                  refine ⟨73273461183061006177075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6252668687621205860443733 73273461183061006177075)
                  ·
                    rfl

theorem cell20_160537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_160537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160537 prefixEnd_160537 := by exact prefixLift 160537
  have htrace : WordTrace (prefixWord ++ tailWord_160537) baseStart_160537 baseEnd_160537 := by
    simpa [prefixWord, tailWord_160537, baseEnd_160537] using wordTrace_append hprefix tailTrace_160537
  have hstable : (prefixWord ++ tailWord_160537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160537).length < 2 ^ (prefixWord ++ tailWord_160537).sum := by decide
  have hdescent : baseEnd_160537 < baseStart_160537 := by decide
  rcases family_descends (prefixWord ++ tailWord_160537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160588 : List Nat := [2, 2, 1, 3, 3, 2, 2, 3, 2]
def baseStart_160588 : Nat := 118140960795 + 160588 * 2 ^ 59
def prefixEnd_160588 : Nat := 4983230072969 + 3 ^ 40 * 160588 * 2
def baseEnd_160588 : Nat := 73296738972731495476867

theorem tailTrace_160588 : CollatzResearch.WordTrace tailWord_160588 prefixEnd_160588 73296738972731495476867 := by
  unfold tailWord_160588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928562771112288545997209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3904750361483051394662945 2928562771112288545997209)
  ·
    refine ⟨2196422078334216409497907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2928562771112288545997209 2196422078334216409497907)
    ·
      refine ⟨3294633117501324614246861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196422078334216409497907 3294633117501324614246861)
      ·
        refine ⟨1235487419062996730342573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3294633117501324614246861 1235487419062996730342573)
        ·
          refine ⟨463307782148623773878465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1235487419062996730342573 463307782148623773878465)
          ·
            refine ⟨347480836611467830408849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463307782148623773878465 347480836611467830408849)
            ·
              refine ⟨260610627458600872806637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347480836611467830408849 260610627458600872806637)
              ·
                refine ⟨97728985296975327302489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260610627458600872806637 97728985296975327302489)
                ·
                  refine ⟨73296738972731495476867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97728985296975327302489 73296738972731495476867)
                  ·
                    rfl

theorem cell20_160588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_160588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160588 prefixEnd_160588 := by exact prefixLift 160588
  have htrace : WordTrace (prefixWord ++ tailWord_160588) baseStart_160588 baseEnd_160588 := by
    simpa [prefixWord, tailWord_160588, baseEnd_160588] using wordTrace_append hprefix tailTrace_160588
  have hstable : (prefixWord ++ tailWord_160588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160588).length < 2 ^ (prefixWord ++ tailWord_160588).sum := by decide
  have hdescent : baseEnd_160588 < baseStart_160588 := by decide
  rcases family_descends (prefixWord ++ tailWord_160588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160599 : List Nat := [1, 1, 3, 2, 4, 2, 7]
def baseStart_160599 : Nat := 118140960795 + 160599 * 2 ^ 59
def prefixEnd_160599 : Nat := 4983230072969 + 3 ^ 40 * 160599 * 2
def baseEnd_160599 : Nat := 8144639963607149567795

theorem tailTrace_160599 : CollatzResearch.WordTrace tailWord_160599 prefixEnd_160599 8144639963607149567795 := by
  unfold tailWord_160599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5857526745184725970644851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3905017830123150647096567 5857526745184725970644851)
  ·
    refine ⟨8786290117777088955967277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5857526745184725970644851 8786290117777088955967277)
    ·
      refine ⟨3294858794166408358487729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8786290117777088955967277 3294858794166408358487729)
      ·
        refine ⟨2471144095624806268865797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3294858794166408358487729 2471144095624806268865797)
        ·
          refine ⟨463339517929651175412337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2471144095624806268865797 463339517929651175412337)
          ·
            refine ⟨347504638447238381559253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463339517929651175412337 347504638447238381559253)
            ·
              refine ⟨8144639963607149567795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 347504638447238381559253 8144639963607149567795)
              ·
                rfl

theorem cell20_160599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 7].length) (baseStart_160599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160599 prefixEnd_160599 := by exact prefixLift 160599
  have htrace : WordTrace (prefixWord ++ tailWord_160599) baseStart_160599 baseEnd_160599 := by
    simpa [prefixWord, tailWord_160599, baseEnd_160599] using wordTrace_append hprefix tailTrace_160599
  have hstable : (prefixWord ++ tailWord_160599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160599).length < 2 ^ (prefixWord ++ tailWord_160599).sum := by decide
  have hdescent : baseEnd_160599 < baseStart_160599 := by decide
  rcases family_descends (prefixWord ++ tailWord_160599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160602 : List Nat := [3, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_160602 : Nat := 118140960795 + 160602 * 2 ^ 59
def prefixEnd_160602 : Nat := 4983230072969 + 3 ^ 40 * 160602 * 2
def baseEnd_160602 : Nat := 73303128954209669010143

theorem tailTrace_160602 : CollatzResearch.WordTrace tailWord_160602 prefixEnd_160602 73303128954209669010143 := by
  unfold tailWord_160602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464409041043464370751015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3905090776115904988669373 1464409041043464370751015)
  ·
    refine ⟨2196613561565196556126523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1464409041043464370751015 2196613561565196556126523)
    ·
      refine ⟨3294920342347794834189785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2196613561565196556126523 3294920342347794834189785)
      ·
        refine ⟨2471190256760846125642339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3294920342347794834189785 2471190256760846125642339)
        ·
          refine ⟨3706785385141269188463509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2471190256760846125642339 3706785385141269188463509)
          ·
            refine ⟨173755564928496993209227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3706785385141269188463509 173755564928496993209227)
            ·
              refine ⟨260633347392745489813841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173755564928496993209227 260633347392745489813841)
              ·
                refine ⟨195475010544559117360381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260633347392745489813841 195475010544559117360381)
                ·
                  refine ⟨73303128954209669010143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195475010544559117360381 73303128954209669010143)
                  ·
                    rfl

theorem cell20_160602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_160602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160602 prefixEnd_160602 := by exact prefixLift 160602
  have htrace : WordTrace (prefixWord ++ tailWord_160602) baseStart_160602 baseEnd_160602 := by
    simpa [prefixWord, tailWord_160602, baseEnd_160602] using wordTrace_append hprefix tailTrace_160602
  have hstable : (prefixWord ++ tailWord_160602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160602).length < 2 ^ (prefixWord ++ tailWord_160602).sum := by decide
  have hdescent : baseEnd_160602 < baseStart_160602 := by decide
  rcases family_descends (prefixWord ++ tailWord_160602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160651 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_160651 : Nat := 118140960795 + 160651 * 2 ^ 59
def prefixEnd_160651 : Nat := 4983230072969 + 3 ^ 40 * 160651 * 2
def baseEnd_160651 : Nat := 73325493889383276376609

theorem tailTrace_160651 : CollatzResearch.WordTrace tailWord_160651 prefixEnd_160651 73325493889383276376609 := by
  unfold tailWord_160651
  simp only [CollatzResearch.WordTrace]
  refine ⟨5859423340996338851537807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3906282227330892567691871 5859423340996338851537807)
  ·
    refine ⟨8789135011494508277306711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5859423340996338851537807 8789135011494508277306711)
    ·
      refine ⟨13183702517241762415960067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8789135011494508277306711 13183702517241762415960067)
      ·
        refine ⟨19775553775862643623940101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13183702517241762415960067 19775553775862643623940101)
        ·
          refine ⟨3707916332974245679488769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19775553775862643623940101 3707916332974245679488769)
          ·
            refine ⟨2780937249730684259616577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3707916332974245679488769 2780937249730684259616577)
            ·
              refine ⟨2085702937298013194712433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2780937249730684259616577 2085702937298013194712433)
              ·
                refine ⟨1564277202973509896034325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2085702937298013194712433 1564277202973509896034325)
                ·
                  refine ⟨73325493889383276376609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1564277202973509896034325 73325493889383276376609)
                  ·
                    rfl

theorem cell20_160651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_160651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160651 prefixEnd_160651 := by exact prefixLift 160651
  have htrace : WordTrace (prefixWord ++ tailWord_160651) baseStart_160651 baseEnd_160651 := by
    simpa [prefixWord, tailWord_160651, baseEnd_160651] using wordTrace_append hprefix tailTrace_160651
  have hstable : (prefixWord ++ tailWord_160651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160651).length < 2 ^ (prefixWord ++ tailWord_160651).sum := by decide
  have hdescent : baseEnd_160651 < baseStart_160651 := by decide
  rcases family_descends (prefixWord ++ tailWord_160651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160730 : List Nat := [3, 1, 1, 2, 4, 3, 1, 5]
def baseStart_160730 : Nat := 118140960795 + 160730 * 2 ^ 59
def prefixEnd_160730 : Nat := 4983230072969 + 3 ^ 40 * 160730 * 2
def baseEnd_160730 : Nat := 24453850547336704247651

theorem tailTrace_160730 : CollatzResearch.WordTrace tailWord_160730 prefixEnd_160730 24453850547336704247651 := by
  unfold tailWord_160730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465576176927533835915911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3908203138473423562442429 1465576176927533835915911)
  ·
    refine ⟨2198364265391300753873867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1465576176927533835915911 2198364265391300753873867)
    ·
      refine ⟨3297546398086951130810801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2198364265391300753873867 3297546398086951130810801)
      ·
        refine ⟨2473159798565213348108101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3297546398086951130810801 2473159798565213348108101)
        ·
          refine ⟨463717462230977502770269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2473159798565213348108101 463717462230977502770269)
          ·
            refine ⟨173894048336616563538851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463717462230977502770269 173894048336616563538851)
            ·
              refine ⟨260841072504924845308277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173894048336616563538851 260841072504924845308277)
              ·
                refine ⟨24453850547336704247651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260841072504924845308277 24453850547336704247651)
                ·
                  rfl

theorem cell20_160730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_160730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160730 prefixEnd_160730 := by exact prefixLift 160730
  have htrace : WordTrace (prefixWord ++ tailWord_160730) baseStart_160730 baseEnd_160730 := by
    simpa [prefixWord, tailWord_160730, baseEnd_160730] using wordTrace_append hprefix tailTrace_160730
  have hstable : (prefixWord ++ tailWord_160730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160730).length < 2 ^ (prefixWord ++ tailWord_160730).sum := by decide
  have hdescent : baseEnd_160730 < baseStart_160730 := by decide
  rcases family_descends (prefixWord ++ tailWord_160730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160761 : List Nat := [1, 2, 1, 3, 1, 3, 4, 3, 2]
def baseStart_160761 : Nat := 118140960795 + 160761 * 2 ^ 59
def prefixEnd_160761 : Nat := 4983230072969 + 3 ^ 40 * 160761 * 2
def baseEnd_160761 : Nat := 73375700886711782709493

theorem tailTrace_160761 : CollatzResearch.WordTrace tailWord_160761 prefixEnd_160761 73375700886711782709493 := by
  unfold tailWord_160761
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863435370597827638042137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3908956913731885092028091 5863435370597827638042137)
  ·
    refine ⟨4397576527948370728531603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5863435370597827638042137 4397576527948370728531603)
    ·
      refine ⟨6596364791922556092797405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4397576527948370728531603 6596364791922556092797405)
      ·
        refine ⟨2473636796970958534799027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6596364791922556092797405 2473636796970958534799027)
        ·
          refine ⟨3710455195456437802198541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473636796970958534799027 3710455195456437802198541)
          ·
            refine ⟨1391420698296164175824453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3710455195456437802198541 1391420698296164175824453)
            ·
              refine ⟨260891380930530782967085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1391420698296164175824453 260891380930530782967085)
              ·
                refine ⟨97834267848949043612657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260891380930530782967085 97834267848949043612657)
                ·
                  refine ⟨73375700886711782709493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97834267848949043612657 73375700886711782709493)
                  ·
                    rfl

theorem cell20_160761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 2].length) (baseStart_160761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160761 prefixEnd_160761 := by exact prefixLift 160761
  have htrace : WordTrace (prefixWord ++ tailWord_160761) baseStart_160761 baseEnd_160761 := by
    simpa [prefixWord, tailWord_160761, baseEnd_160761] using wordTrace_append hprefix tailTrace_160761
  have hstable : (prefixWord ++ tailWord_160761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160761).length < 2 ^ (prefixWord ++ tailWord_160761).sum := by decide
  have hdescent : baseEnd_160761 < baseStart_160761 := by decide
  rcases family_descends (prefixWord ++ tailWord_160761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160765 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_160765 : Nat := 118140960795 + 160765 * 2 ^ 59
def prefixEnd_160765 : Nat := 4983230072969 + 3 ^ 40 * 160765 * 2
def baseEnd_160765 : Nat := 73377526595705546576143

theorem tailTrace_160765 : CollatzResearch.WordTrace tailWord_160765 prefixEnd_160765 73377526595705546576143 := by
  unfold tailWord_160765
  simp only [CollatzResearch.WordTrace]
  refine ⟨5863581262583336321187749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3909054175055557547458499 5863581262583336321187749)
  ·
    refine ⟨1099421486734375560222703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5863581262583336321187749 1099421486734375560222703)
    ·
      refine ⟨1649132230101563340334055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099421486734375560222703 1649132230101563340334055)
      ·
        refine ⟨2473698345152345010501083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649132230101563340334055 2473698345152345010501083)
        ·
          refine ⟨3710547517728517515751625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2473698345152345010501083 3710547517728517515751625)
          ·
            refine ⟨2782910638296388136813719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3710547517728517515751625 2782910638296388136813719)
            ·
              refine ⟨4174365957444582205220579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2782910638296388136813719 4174365957444582205220579)
              ·
                refine ⟨6261548936166873307830869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4174365957444582205220579 6261548936166873307830869)
                ·
                  refine ⟨73377526595705546576143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6261548936166873307830869 73377526595705546576143)
                  ·
                    rfl

theorem cell20_160765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_160765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160765 prefixEnd_160765 := by exact prefixLift 160765
  have htrace : WordTrace (prefixWord ++ tailWord_160765) baseStart_160765 baseEnd_160765 := by
    simpa [prefixWord, tailWord_160765, baseEnd_160765] using wordTrace_append hprefix tailTrace_160765
  have hstable : (prefixWord ++ tailWord_160765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160765).length < 2 ^ (prefixWord ++ tailWord_160765).sum := by decide
  have hdescent : baseEnd_160765 < baseStart_160765 := by decide
  rcases family_descends (prefixWord ++ tailWord_160765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160782 : List Nat := [4, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_160782 : Nat := 118140960795 + 160782 * 2 ^ 59
def prefixEnd_160782 : Nat := 4983230072969 + 3 ^ 40 * 160782 * 2
def baseEnd_160782 : Nat := 73385285858929043009407

theorem tailTrace_160782 : CollatzResearch.WordTrace tailWord_160782 prefixEnd_160782 73385285858929043009407 := by
  unfold tailWord_160782
  simp only [CollatzResearch.WordTrace]
  refine ⟨733025162940218528069575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3909467535681165483037733 733025162940218528069575)
  ·
    refine ⟨1099537744410327792104363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733025162940218528069575 1099537744410327792104363)
    ·
      refine ⟨1649306616615491688156545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099537744410327792104363 1649306616615491688156545)
      ·
        refine ⟨1236979962461618766117409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649306616615491688156545 1236979962461618766117409)
        ·
          refine ⟨927734971846214074588057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1236979962461618766117409 927734971846214074588057)
          ·
            refine ⟨695801228884660555941043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 927734971846214074588057 695801228884660555941043)
            ·
              refine ⟨1043701843326990833911565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695801228884660555941043 1043701843326990833911565)
              ·
                refine ⟨391388191247621562716837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1043701843326990833911565 391388191247621562716837)
                ·
                  refine ⟨73385285858929043009407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391388191247621562716837 73385285858929043009407)
                  ·
                    rfl

theorem cell20_160782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_160782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160782 prefixEnd_160782 := by exact prefixLift 160782
  have htrace : WordTrace (prefixWord ++ tailWord_160782) baseStart_160782 baseEnd_160782 := by
    simpa [prefixWord, tailWord_160782, baseEnd_160782] using wordTrace_append hprefix tailTrace_160782
  have hstable : (prefixWord ++ tailWord_160782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160782).length < 2 ^ (prefixWord ++ tailWord_160782).sum := by decide
  have hdescent : baseEnd_160782 < baseStart_160782 := by decide
  rcases family_descends (prefixWord ++ tailWord_160782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160792 : List Nat := [2, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_160792 : Nat := 118140960795 + 160792 * 2 ^ 59
def prefixEnd_160792 : Nat := 4983230072969 + 3 ^ 40 * 160792 * 2
def baseEnd_160792 : Nat := 73389850131413452676033

theorem tailTrace_160792 : CollatzResearch.WordTrace tailWord_160792 prefixEnd_160792 73389850131413452676033 := by
  unfold tailWord_160792
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932283016742759966210315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3909710688990346621613753 2932283016742759966210315)
  ·
    refine ⟨4398424525114139949315473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2932283016742759966210315 4398424525114139949315473)
    ·
      refine ⟨3298818393835604961986605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4398424525114139949315473 3298818393835604961986605)
      ·
        refine ⟨1237056897688351860744977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3298818393835604961986605 1237056897688351860744977)
        ·
          refine ⟨927792673266263895558733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1237056897688351860744977 927792673266263895558733)
          ·
            refine ⟨347922252474848960834525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 927792673266263895558733 347922252474848960834525)
            ·
              refine ⟨130470844678068360312947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347922252474848960834525 130470844678068360312947)
              ·
                refine ⟨195706267017102540469421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130470844678068360312947 195706267017102540469421)
                ·
                  refine ⟨73389850131413452676033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195706267017102540469421 73389850131413452676033)
                  ·
                    rfl

theorem cell20_160792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_160792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160792 prefixEnd_160792 := by exact prefixLift 160792
  have htrace : WordTrace (prefixWord ++ tailWord_160792) baseStart_160792 baseEnd_160792 := by
    simpa [prefixWord, tailWord_160792, baseEnd_160792] using wordTrace_append hprefix tailTrace_160792
  have hstable : (prefixWord ++ tailWord_160792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160792).length < 2 ^ (prefixWord ++ tailWord_160792).sum := by decide
  have hdescent : baseEnd_160792 < baseStart_160792 := by decide
  rcases family_descends (prefixWord ++ tailWord_160792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160833 : List Nat := [1, 2, 5, 1, 3, 1, 3, 2, 2]
def baseStart_160833 : Nat := 118140960795 + 160833 * 2 ^ 59
def prefixEnd_160833 : Nat := 4983230072969 + 3 ^ 40 * 160833 * 2
def baseEnd_160833 : Nat := 73408563648599532309199

theorem tailTrace_160833 : CollatzResearch.WordTrace tailWord_160833 prefixEnd_160833 73408563648599532309199 := by
  unfold tailWord_160833
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866061426336983934663153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3910707617557989289775435 5866061426336983934663153)
  ·
    refine ⟨4399546069752737950997365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5866061426336983934663153 4399546069752737950997365)
    ·
      refine ⟨412457444039319182906003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4399546069752737950997365 412457444039319182906003)
      ·
        refine ⟨618686166058978774359005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412457444039319182906003 618686166058978774359005)
        ·
          refine ⟨232007312272117040384627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 618686166058978774359005 232007312272117040384627)
          ·
            refine ⟨348010968408175560576941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232007312272117040384627 348010968408175560576941)
            ·
              refine ⟨130504113153065835216353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348010968408175560576941 130504113153065835216353)
              ·
                refine ⟨97878084864799376412265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130504113153065835216353 97878084864799376412265)
                ·
                  refine ⟨73408563648599532309199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97878084864799376412265 73408563648599532309199)
                  ·
                    rfl

theorem cell20_160833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 2, 2].length) (baseStart_160833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160833 prefixEnd_160833 := by exact prefixLift 160833
  have htrace : WordTrace (prefixWord ++ tailWord_160833) baseStart_160833 baseEnd_160833 := by
    simpa [prefixWord, tailWord_160833, baseEnd_160833] using wordTrace_append hprefix tailTrace_160833
  have hstable : (prefixWord ++ tailWord_160833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160833).length < 2 ^ (prefixWord ++ tailWord_160833).sum := by decide
  have hdescent : baseEnd_160833 < baseStart_160833 := by decide
  rcases family_descends (prefixWord ++ tailWord_160833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160841 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 4]
def baseStart_160841 : Nat := 118140960795 + 160841 * 2 ^ 59
def prefixEnd_160841 : Nat := 4983230072969 + 3 ^ 40 * 160841 * 2
def baseEnd_160841 : Nat := 73412215066587060042499

theorem tailTrace_160841 : CollatzResearch.WordTrace tailWord_160841 prefixEnd_160841 73412215066587060042499 := by
  unfold tailWord_160841
  simp only [CollatzResearch.WordTrace]
  refine ⟨5866353210308001300954377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3910902140205334200636251 5866353210308001300954377)
  ·
    refine ⟨4399764907731000975715783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5866353210308001300954377 4399764907731000975715783)
    ·
      refine ⟨6599647361596501463573675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399764907731000975715783 6599647361596501463573675)
      ·
        refine ⟨9899471042394752195360513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6599647361596501463573675 9899471042394752195360513)
        ·
          refine ⟨7424603281796064146520385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9899471042394752195360513 7424603281796064146520385)
          ·
            refine ⟨5568452461347048109890289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7424603281796064146520385 5568452461347048109890289)
            ·
              refine ⟨4176339346010286082417717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5568452461347048109890289 4176339346010286082417717)
              ·
                refine ⟨391531813688464320226661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4176339346010286082417717 391531813688464320226661)
                ·
                  refine ⟨73412215066587060042499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391531813688464320226661 73412215066587060042499)
                  ·
                    rfl

theorem cell20_160841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_160841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160841 prefixEnd_160841 := by exact prefixLift 160841
  have htrace : WordTrace (prefixWord ++ tailWord_160841) baseStart_160841 baseEnd_160841 := by
    simpa [prefixWord, tailWord_160841, baseEnd_160841] using wordTrace_append hprefix tailTrace_160841
  have hstable : (prefixWord ++ tailWord_160841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160841).length < 2 ^ (prefixWord ++ tailWord_160841).sum := by decide
  have hdescent : baseEnd_160841 < baseStart_160841 := by decide
  rcases family_descends (prefixWord ++ tailWord_160841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160885 : List Nat := [1, 3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_160885 : Nat := 118140960795 + 160885 * 2 ^ 59
def prefixEnd_160885 : Nat := 4983230072969 + 3 ^ 40 * 160885 * 2
def baseEnd_160885 : Nat := 73432297865518462575653

theorem tailTrace_160885 : CollatzResearch.WordTrace tailWord_160885 prefixEnd_160885 73432297865518462575653 := by
  unfold tailWord_160885
  simp only [CollatzResearch.WordTrace]
  refine ⟨5867958022148596815556109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3911972014765731210370739 5867958022148596815556109)
  ·
    refine ⟨2200484258305723805833541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5867958022148596815556109 2200484258305723805833541)
    ·
      refine ⟨412590798432323213593789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2200484258305723805833541 412590798432323213593789)
      ·
        refine ⟨154721549412121205097671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412590798432323213593789 154721549412121205097671)
        ·
          refine ⟨232082324118181807646507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154721549412121205097671 232082324118181807646507)
          ·
            refine ⟨348123486177272711469761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232082324118181807646507 348123486177272711469761)
            ·
              refine ⟨261092614632954533602321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348123486177272711469761 261092614632954533602321)
              ·
                refine ⟨195819460974715900201741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261092614632954533602321 195819460974715900201741)
                ·
                  refine ⟨73432297865518462575653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195819460974715900201741 73432297865518462575653)
                  ·
                    rfl

theorem cell20_160885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_160885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160885 prefixEnd_160885 := by exact prefixLift 160885
  have htrace : WordTrace (prefixWord ++ tailWord_160885) baseStart_160885 baseEnd_160885 := by
    simpa [prefixWord, tailWord_160885, baseEnd_160885] using wordTrace_append hprefix tailTrace_160885
  have hstable : (prefixWord ++ tailWord_160885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160885).length < 2 ^ (prefixWord ++ tailWord_160885).sum := by decide
  have hdescent : baseEnd_160885 < baseStart_160885 := by decide
  rcases family_descends (prefixWord ++ tailWord_160885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160920 : List Nat := [2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_160920 : Nat := 118140960795 + 160920 * 2 ^ 59
def prefixEnd_160920 : Nat := 4983230072969 + 3 ^ 40 * 160920 * 2
def baseEnd_160920 : Nat := 24482757606404632136281

theorem tailTrace_160920 : CollatzResearch.WordTrace tailWord_160920 prefixEnd_160920 24482757606404632136281 := by
  unfold tailWord_160920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2934617288510898896540107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3912823051347865195386809 2934617288510898896540107)
  ·
    refine ⟨4401925932766348344810161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2934617288510898896540107 4401925932766348344810161)
    ·
      refine ⟨3301444449574761258607621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4401925932766348344810161 3301444449574761258607621)
      ·
        refine ⟨619020834295267735988929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3301444449574761258607621 619020834295267735988929)
        ·
          refine ⟨464265625721450801991697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619020834295267735988929 464265625721450801991697)
          ·
            refine ⟨348199219291088101493773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464265625721450801991697 348199219291088101493773)
            ·
              refine ⟨130574707234158038060165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348199219291088101493773 130574707234158038060165)
              ·
                refine ⟨24482757606404632136281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130574707234158038060165 24482757606404632136281)
                ·
                  rfl

theorem cell20_160920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_160920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160920 prefixEnd_160920 := by exact prefixLift 160920
  have htrace : WordTrace (prefixWord ++ tailWord_160920) baseStart_160920 baseEnd_160920 := by
    simpa [prefixWord, tailWord_160920, baseEnd_160920] using wordTrace_append hprefix tailTrace_160920
  have hstable : (prefixWord ++ tailWord_160920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160920).length < 2 ^ (prefixWord ++ tailWord_160920).sum := by decide
  have hdescent : baseEnd_160920 < baseStart_160920 := by decide
  rcases family_descends (prefixWord ++ tailWord_160920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160961 : List Nat := [1, 2, 6, 1, 1, 2, 3, 1, 3]
def baseStart_160961 : Nat := 118140960795 + 160961 * 2 ^ 59
def prefixEnd_160961 : Nat := 4983230072969 + 3 ^ 40 * 160961 * 2
def baseEnd_160961 : Nat := 73466986336399976042009

theorem tailTrace_160961 : CollatzResearch.WordTrace tailWord_160961 prefixEnd_160961 73466986336399976042009 := by
  unfold tailWord_160961
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870729969873261795322737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3913819979915507863548491 5870729969873261795322737)
  ·
    refine ⟨4403047477404946346492053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5870729969873261795322737 4403047477404946346492053)
    ·
      refine ⟨206392850503356859991815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4403047477404946346492053 206392850503356859991815)
      ·
        refine ⟨309589275755035289987723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206392850503356859991815 309589275755035289987723)
        ·
          refine ⟨464383913632552934981585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309589275755035289987723 464383913632552934981585)
          ·
            refine ⟨348287935224414701236189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464383913632552934981585 348287935224414701236189)
            ·
              refine ⟨130607975709155512963571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 348287935224414701236189 130607975709155512963571)
              ·
                refine ⟨195911963563733269445357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130607975709155512963571 195911963563733269445357)
                ·
                  refine ⟨73466986336399976042009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195911963563733269445357 73466986336399976042009)
                  ·
                    rfl

theorem cell20_160961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 3, 1, 3].length) (baseStart_160961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_160961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_160961 prefixEnd_160961 := by exact prefixLift 160961
  have htrace : WordTrace (prefixWord ++ tailWord_160961) baseStart_160961 baseEnd_160961 := by
    simpa [prefixWord, tailWord_160961, baseEnd_160961] using wordTrace_append hprefix tailTrace_160961
  have hstable : (prefixWord ++ tailWord_160961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160961).length < 2 ^ (prefixWord ++ tailWord_160961).sum := by decide
  have hdescent : baseEnd_160961 < baseStart_160961 := by decide
  rcases family_descends (prefixWord ++ tailWord_160961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161012 : List Nat := [2, 6, 1, 2, 2, 1, 2, 1, 3]
def baseStart_161012 : Nat := 118140960795 + 161012 * 2 ^ 59
def prefixEnd_161012 : Nat := 4983230072969 + 3 ^ 40 * 161012 * 2
def baseEnd_161012 : Nat := 73490264126070465341801

theorem tailTrace_161012 : CollatzResearch.WordTrace tailWord_161012 prefixEnd_161012 73490264126070465341801 := by
  unfold tailWord_161012
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936295046344248752714645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3915060061792331670286193 2936295046344248752714645)
  ·
    refine ⟨137638830297386660283499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2936295046344248752714645 137638830297386660283499)
    ·
      refine ⟨206458245446079990425249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137638830297386660283499 206458245446079990425249)
      ·
        refine ⟨154843684084559992818937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206458245446079990425249 154843684084559992818937)
        ·
          refine ⟨116132763063419994614203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154843684084559992818937 116132763063419994614203)
          ·
            refine ⟨174199144595129991921305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116132763063419994614203 174199144595129991921305)
            ·
              refine ⟨130649358446347493940979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174199144595129991921305 130649358446347493940979)
              ·
                refine ⟨195974037669521240911469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130649358446347493940979 195974037669521240911469)
                ·
                  refine ⟨73490264126070465341801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195974037669521240911469 73490264126070465341801)
                  ·
                    rfl

theorem cell20_161012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_161012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161012 prefixEnd_161012 := by exact prefixLift 161012
  have htrace : WordTrace (prefixWord ++ tailWord_161012) baseStart_161012 baseEnd_161012 := by
    simpa [prefixWord, tailWord_161012, baseEnd_161012] using wordTrace_append hprefix tailTrace_161012
  have hstable : (prefixWord ++ tailWord_161012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161012).length < 2 ^ (prefixWord ++ tailWord_161012).sum := by decide
  have hdescent : baseEnd_161012 < baseStart_161012 := by decide
  rcases family_descends (prefixWord ++ tailWord_161012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161055 : List Nat := [1, 1, 2, 4, 5, 7]
def baseStart_161055 : Nat := 118140960795 + 161055 * 2 ^ 59
def prefixEnd_161055 : Nat := 4983230072969 + 3 ^ 40 * 161055 * 2
def baseEnd_161055 : Nat := 2722588536953830626233

theorem tailTrace_161055 : CollatzResearch.WordTrace tailWord_161055 prefixEnd_161055 2722588536953830626233 := by
  unfold tailWord_161055
  simp only [CollatzResearch.WordTrace]
  refine ⟨5874158431532715849244619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3916105621021810566163079 5874158431532715849244619)
  ·
    refine ⟨8811237647299073773866929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5874158431532715849244619 8811237647299073773866929)
    ·
      refine ⟨6608428235474305330400197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8811237647299073773866929 6608428235474305330400197)
      ·
        refine ⟨1239080294151432249450037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6608428235474305330400197 1239080294151432249450037)
        ·
          refine ⟨116163777576696773385941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1239080294151432249450037 116163777576696773385941)
          ·
            refine ⟨2722588536953830626233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 116163777576696773385941 2722588536953830626233)
            ·
              rfl

theorem cell20_161055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 7].length) (baseStart_161055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161055 prefixEnd_161055 := by exact prefixLift 161055
  have htrace : WordTrace (prefixWord ++ tailWord_161055) baseStart_161055 baseEnd_161055 := by
    simpa [prefixWord, tailWord_161055, baseEnd_161055] using wordTrace_append hprefix tailTrace_161055
  have hstable : (prefixWord ++ tailWord_161055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161055).length < 2 ^ (prefixWord ++ tailWord_161055).sum := by decide
  have hdescent : baseEnd_161055 < baseStart_161055 := by decide
  rcases family_descends (prefixWord ++ tailWord_161055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161058 : List Nat := [3, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_161058 : Nat := 118140960795 + 161058 * 2 ^ 59
def prefixEnd_161058 : Nat := 4983230072969 + 3 ^ 40 * 161058 * 2
def baseEnd_161058 : Nat := 73511259779498749808279

theorem tailTrace_161058 : CollatzResearch.WordTrace tailWord_161058 prefixEnd_161058 73511259779498749808279 := by
  unfold tailWord_161058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468566962630461840400957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3916178567014564907735885 1468566962630461840400957)
  ·
    refine ⟨550712610986423190150359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1468566962630461840400957 550712610986423190150359)
    ·
      refine ⟨826068916479634785225539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550712610986423190150359 826068916479634785225539)
      ·
        refine ⟨1239103374719452177838309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 826068916479634785225539 1239103374719452177838309)
        ·
          refine ⟨232331882759897283344683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1239103374719452177838309 232331882759897283344683)
          ·
            refine ⟨348497824139845925017025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232331882759897283344683 348497824139845925017025)
            ·
              refine ⟨261373368104884443762769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348497824139845925017025 261373368104884443762769)
              ·
                refine ⟨196030026078663332822077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261373368104884443762769 196030026078663332822077)
                ·
                  refine ⟨73511259779498749808279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196030026078663332822077 73511259779498749808279)
                  ·
                    rfl

theorem cell20_161058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_161058 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161058 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161058 prefixEnd_161058 := by exact prefixLift 161058
  have htrace : WordTrace (prefixWord ++ tailWord_161058) baseStart_161058 baseEnd_161058 := by
    simpa [prefixWord, tailWord_161058, baseEnd_161058] using wordTrace_append hprefix tailTrace_161058
  have hstable : (prefixWord ++ tailWord_161058).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161058).length < 2 ^ (prefixWord ++ tailWord_161058).sum := by decide
  have hdescent : baseEnd_161058 < baseStart_161058 := by decide
  rcases family_descends (prefixWord ++ tailWord_161058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161086 : List Nat := [4, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_161086 : Nat := 118140960795 + 161086 * 2 ^ 59
def prefixEnd_161086 : Nat := 4983230072969 + 3 ^ 40 * 161086 * 2
def baseEnd_161086 : Nat := 73524039742455096874831

theorem tailTrace_161086 : CollatzResearch.WordTrace tailWord_161086 prefixEnd_161086 73524039742455096874831 := by
  unfold tailWord_161086
  simp only [CollatzResearch.WordTrace]
  refine ⟨734411136802551017952889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3916859396280272095748741 734411136802551017952889)
  ·
    refine ⟨550808352601913263464667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 734411136802551017952889 550808352601913263464667)
    ·
      refine ⟨826212528902869895197001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 550808352601913263464667 826212528902869895197001)
      ·
        refine ⟨619659396677152421397751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 826212528902869895197001 619659396677152421397751)
        ·
          refine ⟨929489095015728632096627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 619659396677152421397751 929489095015728632096627)
          ·
            refine ⟨1394233642523592948144941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929489095015728632096627 1394233642523592948144941)
            ·
              refine ⟨522837615946347355554353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1394233642523592948144941 522837615946347355554353)
              ·
                refine ⟨392128211959760516665765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 522837615946347355554353 392128211959760516665765)
                ·
                  refine ⟨73524039742455096874831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392128211959760516665765 73524039742455096874831)
                  ·
                    rfl

theorem cell20_161086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_161086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161086 prefixEnd_161086 := by exact prefixLift 161086
  have htrace : WordTrace (prefixWord ++ tailWord_161086) baseStart_161086 baseEnd_161086 := by
    simpa [prefixWord, tailWord_161086, baseEnd_161086] using wordTrace_append hprefix tailTrace_161086
  have hstable : (prefixWord ++ tailWord_161086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161086).length < 2 ^ (prefixWord ++ tailWord_161086).sum := by decide
  have hdescent : baseEnd_161086 < baseStart_161086 := by decide
  rcases family_descends (prefixWord ++ tailWord_161086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161124 : List Nat := [2, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_161124 : Nat := 118140960795 + 161124 * 2 ^ 59
def prefixEnd_161124 : Nat := 4983230072969 + 3 ^ 40 * 161124 * 2
def baseEnd_161124 : Nat := 73541383977895853608009

theorem tailTrace_161124 : CollatzResearch.WordTrace tailWord_161124 prefixEnd_161124 73541383977895853608009 := by
  unfold tailWord_161124
  simp only [CollatzResearch.WordTrace]
  refine ⟨2938337534141370316753213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3917783378855160422337617 2938337534141370316753213)
  ·
    refine ⟨1101876575303013868782455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2938337534141370316753213 1101876575303013868782455)
    ·
      refine ⟨1652814862954520803173683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1101876575303013868782455 1652814862954520803173683)
      ·
        refine ⟨2479222294431781204760525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1652814862954520803173683 2479222294431781204760525)
        ·
          refine ⟨929708360411917951785197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2479222294431781204760525 929708360411917951785197)
          ·
            refine ⟨348640635154469231919449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 929708360411917951785197 348640635154469231919449)
            ·
              refine ⟨261480476365851923939587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348640635154469231919449 261480476365851923939587)
              ·
                refine ⟨392220714548777885909381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261480476365851923939587 392220714548777885909381)
                ·
                  refine ⟨73541383977895853608009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392220714548777885909381 73541383977895853608009)
                  ·
                    rfl

theorem cell20_161124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_161124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161124 prefixEnd_161124 := by exact prefixLift 161124
  have htrace : WordTrace (prefixWord ++ tailWord_161124) baseStart_161124 baseEnd_161124 := by
    simpa [prefixWord, tailWord_161124, baseEnd_161124] using wordTrace_append hprefix tailTrace_161124
  have hstable : (prefixWord ++ tailWord_161124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161124).length < 2 ^ (prefixWord ++ tailWord_161124).sum := by decide
  have hdescent : baseEnd_161124 < baseStart_161124 := by decide
  rcases family_descends (prefixWord ++ tailWord_161124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161145 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 4]
def baseStart_161145 : Nat := 118140960795 + 161145 * 2 ^ 59
def prefixEnd_161145 : Nat := 4983230072969 + 3 ^ 40 * 161145 * 2
def baseEnd_161145 : Nat := 73550968950113113907923

theorem tailTrace_161145 : CollatzResearch.WordTrace tailWord_161145 prefixEnd_161145 73550968950113113907923 := by
  unfold tailWord_161145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5877441001206661220020889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3918294000804440813347259 5877441001206661220020889)
  ·
    refine ⟨4408080750904995915015667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5877441001206661220020889 4408080750904995915015667)
    ·
      refine ⟨6612121126357493872523501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4408080750904995915015667 6612121126357493872523501)
      ·
        refine ⟨2479545422384060202196313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6612121126357493872523501 2479545422384060202196313)
        ·
          refine ⟨1859659066788045151647235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2479545422384060202196313 1859659066788045151647235)
          ·
            refine ⟨2789488600182067727470853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1859659066788045151647235 2789488600182067727470853)
            ·
              refine ⟨523029112534137698900785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2789488600182067727470853 523029112534137698900785)
              ·
                refine ⟨392271834400603274175589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 523029112534137698900785 392271834400603274175589)
                ·
                  refine ⟨73550968950113113907923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392271834400603274175589 73550968950113113907923)
                  ·
                    rfl

theorem cell20_161145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_161145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161145 prefixEnd_161145 := by exact prefixLift 161145
  have htrace : WordTrace (prefixWord ++ tailWord_161145) baseStart_161145 baseEnd_161145 := by
    simpa [prefixWord, tailWord_161145, baseEnd_161145] using wordTrace_append hprefix tailTrace_161145
  have hstable : (prefixWord ++ tailWord_161145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161145).length < 2 ^ (prefixWord ++ tailWord_161145).sum := by decide
  have hdescent : baseEnd_161145 < baseStart_161145 := by decide
  rcases family_descends (prefixWord ++ tailWord_161145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161228 : List Nat := [2, 2, 1, 4, 2, 9]
def baseStart_161228 : Nat := 118140960795 + 161228 * 2 ^ 59
def prefixEnd_161228 : Nat := 4983230072969 + 3 ^ 40 * 161228 * 2
def baseEnd_161228 : Nat := 2725513052286433857071

theorem tailTrace_161228 : CollatzResearch.WordTrace tailWord_161228 prefixEnd_161228 2725513052286433857071 := by
  unfold tailWord_161228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940234129952983197646169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3920312173270644263528225 2940234129952983197646169)
  ·
    refine ⟨2205175597464737398234627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2940234129952983197646169 2205175597464737398234627)
    ·
      refine ⟨3307763396197106097351941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2205175597464737398234627 3307763396197106097351941)
      ·
        refine ⟨620205636786957393253489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3307763396197106097351941 620205636786957393253489)
        ·
          refine ⟨465154227590218044940117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 620205636786957393253489 465154227590218044940117)
          ·
            refine ⟨2725513052286433857071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 465154227590218044940117 2725513052286433857071)
            ·
              rfl

theorem cell20_161228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 9].length) (baseStart_161228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161228 prefixEnd_161228 := by exact prefixLift 161228
  have htrace : WordTrace (prefixWord ++ tailWord_161228) baseStart_161228 baseEnd_161228 := by
    simpa [prefixWord, tailWord_161228, baseEnd_161228] using wordTrace_append hprefix tailTrace_161228
  have hstable : (prefixWord ++ tailWord_161228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161228).length < 2 ^ (prefixWord ++ tailWord_161228).sum := by decide
  have hdescent : baseEnd_161228 < baseStart_161228 := by decide
  rcases family_descends (prefixWord ++ tailWord_161228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161245 : List Nat := [1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_161245 : Nat := 118140960795 + 161245 * 2 ^ 59
def prefixEnd_161245 : Nat := 4983230072969 + 3 ^ 40 * 161245 * 2
def baseEnd_161245 : Nat := 24532203891652403524727

theorem tailTrace_161245 : CollatzResearch.WordTrace tailWord_161245 prefixEnd_161245 24532203891652403524727 := by
  unfold tailWord_161245
  simp only [CollatzResearch.WordTrace]
  refine ⟨5881088300844378298661189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3920725533896252199107459 5881088300844378298661189)
  ·
    refine ⟨1102704056408320930998973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5881088300844378298661189 1102704056408320930998973)
    ·
      refine ⟨413514021153120349124615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1102704056408320930998973 413514021153120349124615)
      ·
        refine ⟨620271031729680523686923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 413514021153120349124615 620271031729680523686923)
        ·
          refine ⟨930406547594520785530385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 620271031729680523686923 930406547594520785530385)
          ·
            refine ⟨697804910695890589147789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 930406547594520785530385 697804910695890589147789)
            ·
              refine ⟨261676841510958970930421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 697804910695890589147789 261676841510958970930421)
              ·
                refine ⟨24532203891652403524727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 261676841510958970930421 24532203891652403524727)
                ·
                  rfl

theorem cell20_161245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_161245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161245 prefixEnd_161245 := by exact prefixLift 161245
  have htrace : WordTrace (prefixWord ++ tailWord_161245) baseStart_161245 baseEnd_161245 := by
    simpa [prefixWord, tailWord_161245, baseEnd_161245] using wordTrace_append hprefix tailTrace_161245
  have hstable : (prefixWord ++ tailWord_161245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161245).length < 2 ^ (prefixWord ++ tailWord_161245).sum := by decide
  have hdescent : baseEnd_161245 < baseStart_161245 := by decide
  rcases family_descends (prefixWord ++ tailWord_161245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161273 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 5]
def baseStart_161273 : Nat := 118140960795 + 161273 * 2 ^ 59
def prefixEnd_161273 : Nat := 4983230072969 + 3 ^ 40 * 161273 * 2
def baseEnd_161273 : Nat := 73609391637913557640733

theorem tailTrace_161273 : CollatzResearch.WordTrace tailWord_161273 prefixEnd_161273 73609391637913557640733 := by
  unfold tailWord_161273
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882109544742939080680473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3921406363161959387120315 5882109544742939080680473)
  ·
    refine ⟨4411582158557204310510355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5882109544742939080680473 4411582158557204310510355)
    ·
      refine ⟨6617373237835806465765533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4411582158557204310510355 6617373237835806465765533)
      ·
        refine ⟨2481514964188427424662075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6617373237835806465765533 2481514964188427424662075)
        ·
          refine ⟨3722272446282641136993113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481514964188427424662075 3722272446282641136993113)
          ·
            refine ⟨2791704334711980852744835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3722272446282641136993113 2791704334711980852744835)
            ·
              refine ⟨4187556502067971279117253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2791704334711980852744835 4187556502067971279117253)
              ·
                refine ⟨785166844137744614834485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4187556502067971279117253 785166844137744614834485)
                ·
                  refine ⟨73609391637913557640733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785166844137744614834485 73609391637913557640733)
                  ·
                    rfl

theorem cell20_161273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_161273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161273 prefixEnd_161273 := by exact prefixLift 161273
  have htrace : WordTrace (prefixWord ++ tailWord_161273) baseStart_161273 baseEnd_161273 := by
    simpa [prefixWord, tailWord_161273, baseEnd_161273] using wordTrace_append hprefix tailTrace_161273
  have hstable : (prefixWord ++ tailWord_161273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161273).length < 2 ^ (prefixWord ++ tailWord_161273).sum := by decide
  have hdescent : baseEnd_161273 < baseStart_161273 := by decide
  rcases family_descends (prefixWord ++ tailWord_161273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161276 : List Nat := [2, 2, 2, 1, 2, 1, 3, 5, 2]
def baseStart_161276 : Nat := 118140960795 + 161276 * 2 ^ 59
def prefixEnd_161276 : Nat := 4983230072969 + 3 ^ 40 * 161276 * 2
def baseEnd_161276 : Nat := 73610760919658880540721

theorem tailTrace_161276 : CollatzResearch.WordTrace tailWord_161276 prefixEnd_161276 73610760919658880540721 := by
  unfold tailWord_161276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941109481866035296519841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3921479309154713728693121 2941109481866035296519841)
  ·
    refine ⟨2205832111399526472389881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2941109481866035296519841 2205832111399526472389881)
    ·
      refine ⟨1654374083549644854292411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2205832111399526472389881 1654374083549644854292411)
      ·
        refine ⟨2481561125324467281438617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1654374083549644854292411 2481561125324467281438617)
        ·
          refine ⟨1861170843993350461078963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2481561125324467281438617 1861170843993350461078963)
          ·
            refine ⟨2791756265990025691618445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1861170843993350461078963 2791756265990025691618445)
            ·
              refine ⟨1046908599746259634356917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2791756265990025691618445 1046908599746259634356917)
              ·
                refine ⟨98147681226211840720961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1046908599746259634356917 98147681226211840720961)
                ·
                  refine ⟨73610760919658880540721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98147681226211840720961 73610760919658880540721)
                  ·
                    rfl

theorem cell20_161276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_161276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161276 prefixEnd_161276 := by exact prefixLift 161276
  have htrace : WordTrace (prefixWord ++ tailWord_161276) baseStart_161276 baseEnd_161276 := by
    simpa [prefixWord, tailWord_161276, baseEnd_161276] using wordTrace_append hprefix tailTrace_161276
  have hstable : (prefixWord ++ tailWord_161276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161276).length < 2 ^ (prefixWord ++ tailWord_161276).sum := by decide
  have hdescent : baseEnd_161276 < baseStart_161276 := by decide
  rcases family_descends (prefixWord ++ tailWord_161276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161290 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_161290 : Nat := 118140960795 + 161290 * 2 ^ 59
def prefixEnd_161290 : Nat := 4983230072969 + 3 ^ 40 * 161290 * 2
def baseEnd_161290 : Nat := 73617150901137054073997

theorem tailTrace_161290 : CollatzResearch.WordTrace tailWord_161290 prefixEnd_161290 73617150901137054073997 := by
  unfold tailWord_161290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1470682396420337746012331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3921819723787567322699549 1470682396420337746012331)
  ·
    refine ⟨2206023594630506619018497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1470682396420337746012331 2206023594630506619018497)
    ·
      refine ⟨1654517695972879964263873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2206023594630506619018497 1654517695972879964263873)
      ·
        refine ⟨1240888271979659973197905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1654517695972879964263873 1240888271979659973197905)
        ·
          refine ⟨930666203984744979898429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1240888271979659973197905 930666203984744979898429)
          ·
            refine ⟨348999826494279367461911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 930666203984744979898429 348999826494279367461911)
            ·
              refine ⟨523499739741419051192867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348999826494279367461911 523499739741419051192867)
              ·
                refine ⟨785249609612128576789301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 523499739741419051192867 785249609612128576789301)
                ·
                  refine ⟨73617150901137054073997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785249609612128576789301 73617150901137054073997)
                  ·
                    rfl

theorem cell20_161290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_161290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161290 prefixEnd_161290 := by exact prefixLift 161290
  have htrace : WordTrace (prefixWord ++ tailWord_161290) baseStart_161290 baseEnd_161290 := by
    simpa [prefixWord, tailWord_161290, baseEnd_161290] using wordTrace_append hprefix tailTrace_161290
  have hstable : (prefixWord ++ tailWord_161290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161290).length < 2 ^ (prefixWord ++ tailWord_161290).sum := by decide
  have hdescent : baseEnd_161290 < baseStart_161290 := by decide
  rcases family_descends (prefixWord ++ tailWord_161290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161297 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 4]
def baseStart_161297 : Nat := 118140960795 + 161297 * 2 ^ 59
def prefixEnd_161297 : Nat := 4983230072969 + 3 ^ 40 * 161297 * 2
def baseEnd_161297 : Nat := 73620345891876140840635

theorem tailTrace_161297 : CollatzResearch.WordTrace tailWord_161297 prefixEnd_161297 73620345891876140840635 := by
  unfold tailWord_161297
  simp only [CollatzResearch.WordTrace]
  refine ⟨5882984896655991179554145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3921989931103994119702763 5882984896655991179554145)
  ·
    refine ⟨4412238672491993384665609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5882984896655991179554145 4412238672491993384665609)
    ·
      refine ⟨3309179004368995038499207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4412238672491993384665609 3309179004368995038499207)
      ·
        refine ⟨4963768506553492557748811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3309179004368995038499207 4963768506553492557748811)
        ·
          refine ⟨7445652759830238836623217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4963768506553492557748811 7445652759830238836623217)
          ·
            refine ⟨5584239569872679127467413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7445652759830238836623217 5584239569872679127467413)
            ·
              refine ⟨261761229837781834100035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5584239569872679127467413 261761229837781834100035)
              ·
                refine ⟨392641844756672751150053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261761229837781834100035 392641844756672751150053)
                ·
                  refine ⟨73620345891876140840635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 392641844756672751150053 73620345891876140840635)
                  ·
                    rfl

theorem cell20_161297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 4].length) (baseStart_161297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161297 prefixEnd_161297 := by exact prefixLift 161297
  have htrace : WordTrace (prefixWord ++ tailWord_161297) baseStart_161297 baseEnd_161297 := by
    simpa [prefixWord, tailWord_161297, baseEnd_161297] using wordTrace_append hprefix tailTrace_161297
  have hstable : (prefixWord ++ tailWord_161297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161297).length < 2 ^ (prefixWord ++ tailWord_161297).sum := by decide
  have hdescent : baseEnd_161297 < baseStart_161297 := by decide
  rcases family_descends (prefixWord ++ tailWord_161297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161331 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 2]
def baseStart_161331 : Nat := 118140960795 + 161331 * 2 ^ 59
def prefixEnd_161331 : Nat := 4983230072969 + 3 ^ 40 * 161331 * 2
def baseEnd_161331 : Nat := 73635864418323133707163

theorem tailTrace_161331 : CollatzResearch.WordTrace tailWord_161331 prefixEnd_161331 73635864418323133707163 := by
  unfold tailWord_161331
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884224978532814986291847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3922816652355209990861231 5884224978532814986291847)
  ·
    refine ⟨8826337467799222479437771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5884224978532814986291847 8826337467799222479437771)
    ·
      refine ⟨13239506201698833719156657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8826337467799222479437771 13239506201698833719156657)
      ·
        refine ⟨9929629651274125289367493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13239506201698833719156657 9929629651274125289367493)
        ·
          refine ⟨1861805559613898491756405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9929629651274125289367493 1861805559613898491756405)
          ·
            refine ⟨174544271213802983602163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1861805559613898491756405 174544271213802983602163)
            ·
              refine ⟨261816406820704475403245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174544271213802983602163 261816406820704475403245)
              ·
                refine ⟨98181152557764178276217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261816406820704475403245 98181152557764178276217)
                ·
                  refine ⟨73635864418323133707163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98181152557764178276217 73635864418323133707163)
                  ·
                    rfl

theorem cell20_161331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2].length) (baseStart_161331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161331 prefixEnd_161331 := by exact prefixLift 161331
  have htrace : WordTrace (prefixWord ++ tailWord_161331) baseStart_161331 baseEnd_161331 := by
    simpa [prefixWord, tailWord_161331, baseEnd_161331] using wordTrace_append hprefix tailTrace_161331
  have hstable : (prefixWord ++ tailWord_161331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161331).length < 2 ^ (prefixWord ++ tailWord_161331).sum := by decide
  have hdescent : baseEnd_161331 < baseStart_161331 := by decide
  rcases family_descends (prefixWord ++ tailWord_161331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161349 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_161349 : Nat := 118140960795 + 161349 * 2 ^ 59
def prefixEnd_161349 : Nat := 4983230072969 + 3 ^ 40 * 161349 * 2
def baseEnd_161349 : Nat := 73644080108795071107089

theorem tailTrace_161349 : CollatzResearch.WordTrace tailWord_161349 prefixEnd_161349 73644080108795071107089 := by
  unfold tailWord_161349
  simp only [CollatzResearch.WordTrace]
  refine ⟨5884881492467604060447101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3923254328311736040298067 5884881492467604060447101)
  ·
    refine ⟨2206830559675351522667663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5884881492467604060447101 2206830559675351522667663)
    ·
      refine ⟨3310245839513027284001495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2206830559675351522667663 3310245839513027284001495)
      ·
        refine ⟨4965368759269540926002243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3310245839513027284001495 4965368759269540926002243)
        ·
          refine ⟨7448053138904311389003365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4965368759269540926002243 7448053138904311389003365)
          ·
            refine ⟨1396509963544558385438131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7448053138904311389003365 1396509963544558385438131)
            ·
              refine ⟨2094764945316837578157197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1396509963544558385438131 2094764945316837578157197)
              ·
                refine ⟨785536854493814091808949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2094764945316837578157197 785536854493814091808949)
                ·
                  refine ⟨73644080108795071107089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 785536854493814091808949 73644080108795071107089)
                  ·
                    rfl

theorem cell20_161349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_161349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161349 prefixEnd_161349 := by exact prefixLift 161349
  have htrace : WordTrace (prefixWord ++ tailWord_161349) baseStart_161349 baseEnd_161349 := by
    simpa [prefixWord, tailWord_161349, baseEnd_161349] using wordTrace_append hprefix tailTrace_161349
  have hstable : (prefixWord ++ tailWord_161349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161349).length < 2 ^ (prefixWord ++ tailWord_161349).sum := by decide
  have hdescent : baseEnd_161349 < baseStart_161349 := by decide
  rcases family_descends (prefixWord ++ tailWord_161349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161362 : List Nat := [3, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_161362 : Nat := 118140960795 + 161362 * 2 ^ 59
def prefixEnd_161362 : Nat := 4983230072969 + 3 ^ 40 * 161362 * 2
def baseEnd_161362 : Nat := 73650013663024803673703

theorem tailTrace_161362 : CollatzResearch.WordTrace tailWord_161362 prefixEnd_161362 73650013663024803673703 := by
  unfold tailWord_161362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471338910355126820167585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3923570427613671520446893 1471338910355126820167585)
  ·
    refine ⟨1103504182766345115125689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1471338910355126820167585 1103504182766345115125689)
    ·
      refine ⟨827628137074758836344267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1103504182766345115125689 827628137074758836344267)
      ·
        refine ⟨1241442205612138254516401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 827628137074758836344267 1241442205612138254516401)
        ·
          refine ⟨931081654209103690887301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1241442205612138254516401 931081654209103690887301)
          ·
            refine ⟨174577810164206942041369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 931081654209103690887301 174577810164206942041369)
            ·
              refine ⟨130933357623155206531027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174577810164206942041369 130933357623155206531027)
              ·
                refine ⟨196400036434732809796541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130933357623155206531027 196400036434732809796541)
                ·
                  refine ⟨73650013663024803673703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196400036434732809796541 73650013663024803673703)
                  ·
                    rfl

theorem cell20_161362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_161362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161362 prefixEnd_161362 := by exact prefixLift 161362
  have htrace : WordTrace (prefixWord ++ tailWord_161362) baseStart_161362 baseEnd_161362 := by
    simpa [prefixWord, tailWord_161362, baseEnd_161362] using wordTrace_append hprefix tailTrace_161362
  have hstable : (prefixWord ++ tailWord_161362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161362).length < 2 ^ (prefixWord ++ tailWord_161362).sum := by decide
  have hdescent : baseEnd_161362 < baseStart_161362 := by decide
  rcases family_descends (prefixWord ++ tailWord_161362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161380 : List Nat := [2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_161380 : Nat := 118140960795 + 161380 * 2 ^ 59
def prefixEnd_161380 : Nat := 4983230072969 + 3 ^ 40 * 161380 * 2
def baseEnd_161380 : Nat := 24552743117832247024543

theorem tailTrace_161380 : CollatzResearch.WordTrace tailWord_161380 prefixEnd_161380 24552743117832247024543 := by
  unfold tailWord_161380
  simp only [CollatzResearch.WordTrace]
  refine ⟨2943006077677648177412797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3924008103570197569883729 2943006077677648177412797)
  ·
    refine ⟨1103627279129118066529799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2943006077677648177412797 1103627279129118066529799)
    ·
      refine ⟨1655440918693677099794699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103627279129118066529799 1655440918693677099794699)
      ·
        refine ⟨2483161378040515649692049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655440918693677099794699 2483161378040515649692049)
        ·
          refine ⟨1862371033530386737269037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2483161378040515649692049 1862371033530386737269037)
          ·
            refine ⟨698389137573895026475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1862371033530386737269037 698389137573895026475889)
            ·
              refine ⟨523791853180421269856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698389137573895026475889 523791853180421269856917)
              ·
                refine ⟨24552743117832247024543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 523791853180421269856917 24552743117832247024543)
                ·
                  rfl

theorem cell20_161380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_161380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161380 prefixEnd_161380 := by exact prefixLift 161380
  have htrace : WordTrace (prefixWord ++ tailWord_161380) baseStart_161380 baseEnd_161380 := by
    simpa [prefixWord, tailWord_161380, baseEnd_161380] using wordTrace_append hprefix tailTrace_161380
  have hstable : (prefixWord ++ tailWord_161380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161380).length < 2 ^ (prefixWord ++ tailWord_161380).sum := by decide
  have hdescent : baseEnd_161380 < baseStart_161380 := by decide
  rcases family_descends (prefixWord ++ tailWord_161380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161462 : List Nat := [5, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_161462 : Nat := 118140960795 + 161462 * 2 ^ 59
def prefixEnd_161462 : Nat := 4983230072969 + 3 ^ 40 * 161462 * 2
def baseEnd_161462 : Nat := 73695656387868900339961

theorem tailTrace_161462 : CollatzResearch.WordTrace tailWord_161462 prefixEnd_161462 73695656387868900339961 := by
  unfold tailWord_161462
  simp only [CollatzResearch.WordTrace]
  refine ⟨368062683816139022456915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3926001960705482906207093 368062683816139022456915)
  ·
    refine ⟨552094025724208533685373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 368062683816139022456915 552094025724208533685373)
    ·
      refine ⟨207035259646578200132015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 552094025724208533685373 207035259646578200132015)
      ·
        refine ⟨310552889469867300198023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207035259646578200132015 310552889469867300198023)
        ·
          refine ⟨465829334204800950297035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 310552889469867300198023 465829334204800950297035)
          ·
            refine ⟨698744001307201425445553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465829334204800950297035 698744001307201425445553)
            ·
              refine ⟨524058000980401069084165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698744001307201425445553 524058000980401069084165)
              ·
                refine ⟨98260875183825200453281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524058000980401069084165 98260875183825200453281)
                ·
                  refine ⟨73695656387868900339961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98260875183825200453281 73695656387868900339961)
                  ·
                    rfl

theorem cell20_161462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_161462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161462 prefixEnd_161462 := by exact prefixLift 161462
  have htrace : WordTrace (prefixWord ++ tailWord_161462) baseStart_161462 baseEnd_161462 := by
    simpa [prefixWord, tailWord_161462, baseEnd_161462] using wordTrace_append hprefix tailTrace_161462
  have hstable : (prefixWord ++ tailWord_161462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161462).length < 2 ^ (prefixWord ++ tailWord_161462).sum := by decide
  have hdescent : baseEnd_161462 < baseStart_161462 := by decide
  rcases family_descends (prefixWord ++ tailWord_161462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161466 : List Nat := [3, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_161466 : Nat := 118140960795 + 161466 * 2 ^ 59
def prefixEnd_161466 : Nat := 4983230072969 + 3 ^ 40 * 161466 * 2
def baseEnd_161466 : Nat := 73697482096862664206611

theorem tailTrace_161466 : CollatzResearch.WordTrace tailWord_161466 prefixEnd_161466 73697482096862664206611 := by
  unfold tailWord_161466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472287208260933260614063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3926099222029155361637501 1472287208260933260614063)
  ·
    refine ⟨2208430812391399890921095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472287208260933260614063 2208430812391399890921095)
    ·
      refine ⟨3312646218587099836381643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208430812391399890921095 3312646218587099836381643)
      ·
        refine ⟨4968969327880649754572465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3312646218587099836381643 4968969327880649754572465)
        ·
          refine ⟨3726726995910487315929349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4968969327880649754572465 3726726995910487315929349)
          ·
            refine ⟨698761311733216371736753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3726726995910487315929349 698761311733216371736753)
            ·
              refine ⟨524070983799912278802565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 698761311733216371736753 524070983799912278802565)
              ·
                refine ⟨98263309462483552275481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524070983799912278802565 98263309462483552275481)
                ·
                  refine ⟨73697482096862664206611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98263309462483552275481 73697482096862664206611)
                  ·
                    rfl

theorem cell20_161466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_161466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161466 prefixEnd_161466 := by exact prefixLift 161466
  have htrace : WordTrace (prefixWord ++ tailWord_161466) baseStart_161466 baseEnd_161466 := by
    simpa [prefixWord, tailWord_161466, baseEnd_161466] using wordTrace_append hprefix tailTrace_161466
  have hstable : (prefixWord ++ tailWord_161466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161466).length < 2 ^ (prefixWord ++ tailWord_161466).sum := by decide
  have hdescent : baseEnd_161466 < baseStart_161466 := by decide
  rcases family_descends (prefixWord ++ tailWord_161466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161490 : List Nat := [3, 2, 2, 2, 2, 3, 2, 4]
def baseStart_161490 : Nat := 118140960795 + 161490 * 2 ^ 59
def prefixEnd_161490 : Nat := 4983230072969 + 3 ^ 40 * 161490 * 2
def baseEnd_161490 : Nat := 24569478783608415802171

theorem tailTrace_161490 : CollatzResearch.WordTrace tailWord_161490 prefixEnd_161490 24569478783608415802171 := by
  unfold tailWord_161490
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472506046239196285332481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3926682789971190094219949 1472506046239196285332481)
  ·
    refine ⟨1104379534679397213999361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1472506046239196285332481 1104379534679397213999361)
    ·
      refine ⟨828284651009547910499521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104379534679397213999361 828284651009547910499521)
      ·
        refine ⟨621213488257160932874641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 828284651009547910499521 621213488257160932874641)
        ·
          refine ⟨465910116192870699655981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621213488257160932874641 465910116192870699655981)
          ·
            refine ⟨174716293572326512370993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 465910116192870699655981 174716293572326512370993)
            ·
              refine ⟨131037220179244884278245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174716293572326512370993 131037220179244884278245)
              ·
                refine ⟨24569478783608415802171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131037220179244884278245 24569478783608415802171)
                ·
                  rfl

theorem cell20_161490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_161490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161490 prefixEnd_161490 := by exact prefixLift 161490
  have htrace : WordTrace (prefixWord ++ tailWord_161490) baseStart_161490 baseEnd_161490 := by
    simpa [prefixWord, tailWord_161490, baseEnd_161490] using wordTrace_append hprefix tailTrace_161490
  have hstable : (prefixWord ++ tailWord_161490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161490).length < 2 ^ (prefixWord ++ tailWord_161490).sum := by decide
  have hdescent : baseEnd_161490 < baseStart_161490 := by decide
  rcases family_descends (prefixWord ++ tailWord_161490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161504 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 2]
def baseStart_161504 : Nat := 118140960795 + 161504 * 2 ^ 59
def prefixEnd_161504 : Nat := 4983230072969 + 3 ^ 40 * 161504 * 2
def baseEnd_161504 : Nat := 73714826332303420939789

theorem tailTrace_161504 : CollatzResearch.WordTrace tailWord_161504 prefixEnd_161504 73714826332303420939789 := by
  unfold tailWord_161504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945267403453032766169783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3927023204604043688226377 2945267403453032766169783)
  ·
    refine ⟨4417901105179549149254675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2945267403453032766169783 4417901105179549149254675)
    ·
      refine ⟨6626851657769323723882013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4417901105179549149254675 6626851657769323723882013)
      ·
        refine ⟨2485069371663496396455755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6626851657769323723882013 2485069371663496396455755)
        ·
          refine ⟨3727604057495244594683633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2485069371663496396455755 3727604057495244594683633)
          ·
            refine ⟨2795703043121433446012725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3727604057495244594683633 2795703043121433446012725)
            ·
              refine ⟨262097160292634385563693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2795703043121433446012725 262097160292634385563693)
              ·
                refine ⟨98286435109737894586385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262097160292634385563693 98286435109737894586385)
                ·
                  refine ⟨73714826332303420939789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98286435109737894586385 73714826332303420939789)
                  ·
                    rfl

theorem cell20_161504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 2].length) (baseStart_161504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161504 prefixEnd_161504 := by exact prefixLift 161504
  have htrace : WordTrace (prefixWord ++ tailWord_161504) baseStart_161504 baseEnd_161504 := by
    simpa [prefixWord, tailWord_161504, baseEnd_161504] using wordTrace_append hprefix tailTrace_161504
  have hstable : (prefixWord ++ tailWord_161504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161504).length < 2 ^ (prefixWord ++ tailWord_161504).sum := by decide
  have hdescent : baseEnd_161504 < baseStart_161504 := by decide
  rcases family_descends (prefixWord ++ tailWord_161504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161515 : List Nat := [1, 1, 1, 1, 2, 4, 10]
def baseStart_161515 : Nat := 118140960795 + 161515 * 2 ^ 59
def prefixEnd_161515 : Nat := 4983230072969 + 3 ^ 40 * 161515 * 2
def baseEnd_161515 : Nat := 8191094114670696841453

theorem tailTrace_161515 : CollatzResearch.WordTrace tailWord_161515 prefixEnd_161515 8191094114670696841453 := by
  unfold tailWord_161515
  simp only [CollatzResearch.WordTrace]
  refine ⟨5890936009866214410989999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3927290673244142940659999 5890936009866214410989999)
  ·
    refine ⟨8836404014799321616484999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5890936009866214410989999 8836404014799321616484999)
    ·
      refine ⟨13254606022198982424727499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8836404014799321616484999 13254606022198982424727499)
      ·
        refine ⟨19881909033298473637091249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13254606022198982424727499 19881909033298473637091249)
        ·
          refine ⟨14911431774973855227818437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19881909033298473637091249 14911431774973855227818437)
          ·
            refine ⟨2795893457807597855215957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14911431774973855227818437 2795893457807597855215957)
            ·
              refine ⟨8191094114670696841453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2795893457807597855215957 8191094114670696841453)
              ·
                rfl

theorem cell20_161515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_161515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161515 prefixEnd_161515 := by exact prefixLift 161515
  have htrace : WordTrace (prefixWord ++ tailWord_161515) baseStart_161515 baseEnd_161515 := by
    simpa [prefixWord, tailWord_161515, baseEnd_161515] using wordTrace_append hprefix tailTrace_161515
  have hstable : (prefixWord ++ tailWord_161515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161515).length < 2 ^ (prefixWord ++ tailWord_161515).sum := by decide
  have hdescent : baseEnd_161515 < baseStart_161515 := by decide
  rcases family_descends (prefixWord ++ tailWord_161515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161518 : List Nat := [4, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_161518 : Nat := 118140960795 + 161518 * 2 ^ 59
def prefixEnd_161518 : Nat := 4983230072969 + 3 ^ 40 * 161518 * 2
def baseEnd_161518 : Nat := 73721216313781594473065

theorem tailTrace_161518 : CollatzResearch.WordTrace tailWord_161518 prefixEnd_161518 73721216313781594473065 := by
  unfold tailWord_161518
  simp only [CollatzResearch.WordTrace]
  refine ⟨736380678606918240418651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3927363619236897282232805 736380678606918240418651)
  ·
    refine ⟨1104571017910377360627977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 736380678606918240418651 1104571017910377360627977)
    ·
      refine ⟨828428263432783020470983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1104571017910377360627977 828428263432783020470983)
      ·
        refine ⟨1242642395149174530706475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828428263432783020470983 1242642395149174530706475)
        ·
          refine ⟨1863963592723761796059713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1242642395149174530706475 1863963592723761796059713)
          ·
            refine ⟨1397972694542821347044785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1863963592723761796059713 1397972694542821347044785)
            ·
              refine ⟨1048479520907116010283589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1397972694542821347044785 1048479520907116010283589)
              ·
                refine ⟨196589910170084251928173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1048479520907116010283589 196589910170084251928173)
                ·
                  refine ⟨73721216313781594473065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196589910170084251928173 73721216313781594473065)
                  ·
                    rfl

theorem cell20_161518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_161518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161518 prefixEnd_161518 := by exact prefixLift 161518
  have htrace : WordTrace (prefixWord ++ tailWord_161518) baseStart_161518 baseEnd_161518 := by
    simpa [prefixWord, tailWord_161518, baseEnd_161518] using wordTrace_append hprefix tailTrace_161518
  have hstable : (prefixWord ++ tailWord_161518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161518).length < 2 ^ (prefixWord ++ tailWord_161518).sum := by decide
  have hdescent : baseEnd_161518 < baseStart_161518 := by decide
  rcases family_descends (prefixWord ++ tailWord_161518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161521 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 2]
def baseStart_161521 : Nat := 118140960795 + 161521 * 2 ^ 59
def prefixEnd_161521 : Nat := 4983230072969 + 3 ^ 40 * 161521 * 2
def baseEnd_161521 : Nat := 73722585595526917373053

theorem tailTrace_161521 : CollatzResearch.WordTrace tailWord_161521 prefixEnd_161521 73722585595526917373053 := by
  unfold tailWord_161521
  simp only [CollatzResearch.WordTrace]
  refine ⟨5891154847844477435708417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3927436565229651623805611 5891154847844477435708417)
  ·
    refine ⟨4418366135883358076781313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5891154847844477435708417 4418366135883358076781313)
    ·
      refine ⟨3313774601912518557585985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4418366135883358076781313 3313774601912518557585985)
      ·
        refine ⟨2485330951434388918189489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3313774601912518557585985 2485330951434388918189489)
        ·
          refine ⟨1863998213575791688642117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2485330951434388918189489 1863998213575791688642117)
          ·
            refine ⟨349499665045460941620397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1863998213575791688642117 349499665045460941620397)
            ·
              refine ⟨131062374392047853107649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349499665045460941620397 131062374392047853107649)
              ·
                refine ⟨98296780794035889830737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131062374392047853107649 98296780794035889830737)
                ·
                  refine ⟨73722585595526917373053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98296780794035889830737 73722585595526917373053)
                  ·
                    rfl

theorem cell20_161521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_161521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161521 prefixEnd_161521 := by exact prefixLift 161521
  have htrace : WordTrace (prefixWord ++ tailWord_161521) baseStart_161521 baseEnd_161521 := by
    simpa [prefixWord, tailWord_161521, baseEnd_161521] using wordTrace_append hprefix tailTrace_161521
  have hstable : (prefixWord ++ tailWord_161521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161521).length < 2 ^ (prefixWord ++ tailWord_161521).sum := by decide
  have hdescent : baseEnd_161521 < baseStart_161521 := by decide
  rcases family_descends (prefixWord ++ tailWord_161521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161532 : List Nat := [2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_161532 : Nat := 118140960795 + 161532 * 2 ^ 59
def prefixEnd_161532 : Nat := 4983230072969 + 3 ^ 40 * 161532 * 2
def baseEnd_161532 : Nat := 24575868765086589335447

theorem tailTrace_161532 : CollatzResearch.WordTrace tailWord_161532 prefixEnd_161532 24575868765086589335447 := by
  unfold tailWord_161532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2945778025402313157179425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3927704033869750876239233 2945778025402313157179425)
  ·
    refine ⟨2209333519051734867884569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2945778025402313157179425 2209333519051734867884569)
    ·
      refine ⟨1657000139288801150913427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2209333519051734867884569 1657000139288801150913427)
      ·
        refine ⟨2485500208933201726370141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1657000139288801150913427 2485500208933201726370141)
        ·
          refine ⟨932062578349950647388803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2485500208933201726370141 932062578349950647388803)
          ·
            refine ⟨1398093867524925971083205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932062578349950647388803 1398093867524925971083205)
            ·
              refine ⟨262142600160923619578101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1398093867524925971083205 262142600160923619578101)
              ·
                refine ⟨24575868765086589335447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262142600160923619578101 24575868765086589335447)
                ·
                  rfl

theorem cell20_161532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_161532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161532 prefixEnd_161532 := by exact prefixLift 161532
  have htrace : WordTrace (prefixWord ++ tailWord_161532) baseStart_161532 baseEnd_161532 := by
    simpa [prefixWord, tailWord_161532, baseEnd_161532] using wordTrace_append hprefix tailTrace_161532
  have hstable : (prefixWord ++ tailWord_161532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161532).length < 2 ^ (prefixWord ++ tailWord_161532).sum := by decide
  have hdescent : baseEnd_161532 < baseStart_161532 := by decide
  rcases family_descends (prefixWord ++ tailWord_161532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161566 : List Nat := [4, 3, 2, 2, 1, 8]
def baseStart_161566 : Nat := 118140960795 + 161566 * 2 ^ 59
def prefixEnd_161566 : Nat := 4983230072969 + 3 ^ 40 * 161566 * 2
def baseEnd_161566 : Nat := 2731226845248398550847

theorem tailTrace_161566 : CollatzResearch.WordTrace tailWord_161566 prefixEnd_161566 2731226845248398550847 := by
  unfold tailWord_161566
  simp only [CollatzResearch.WordTrace]
  refine ⟨736599516585181265137069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3928530755120966747397701 736599516585181265137069)
  ·
    refine ⟨276224818719442974426401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 736599516585181265137069 276224818719442974426401)
    ·
      refine ⟨207168614039582230819801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276224818719442974426401 207168614039582230819801)
      ·
        refine ⟨155376460529686673114851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207168614039582230819801 155376460529686673114851)
        ·
          refine ⟨233064690794530009672277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155376460529686673114851 233064690794530009672277)
          ·
            refine ⟨2731226845248398550847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 233064690794530009672277 2731226845248398550847)
            ·
              rfl

theorem cell20_161566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 8].length) (baseStart_161566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161566 prefixEnd_161566 := by exact prefixLift 161566
  have htrace : WordTrace (prefixWord ++ tailWord_161566) baseStart_161566 baseEnd_161566 := by
    simpa [prefixWord, tailWord_161566, baseEnd_161566] using wordTrace_append hprefix tailTrace_161566
  have hstable : (prefixWord ++ tailWord_161566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161566).length < 2 ^ (prefixWord ++ tailWord_161566).sum := by decide
  have hdescent : baseEnd_161566 < baseStart_161566 := by decide
  rcases family_descends (prefixWord ++ tailWord_161566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161576 : List Nat := [2, 1, 5, 1, 1, 4, 2, 2, 2]
def baseStart_161576 : Nat := 118140960795 + 161576 * 2 ^ 59
def prefixEnd_161576 : Nat := 4983230072969 + 3 ^ 40 * 161576 * 2
def baseEnd_161576 : Nat := 73747689094191170539495

theorem tailTrace_161576 : CollatzResearch.WordTrace tailWord_161576 prefixEnd_161576 73747689094191170539495 := by
  unfold tailWord_161576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946580431322610914480291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3928773908430147885973721 2946580431322610914480291)
  ·
    refine ⟨4419870646983916371720437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2946580431322610914480291 4419870646983916371720437)
    ·
      refine ⟨414362873154742159848791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4419870646983916371720437 414362873154742159848791)
      ·
        refine ⟨621544309732113239773187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414362873154742159848791 621544309732113239773187)
        ·
          refine ⟨932316464598169859659781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621544309732113239773187 932316464598169859659781)
          ·
            refine ⟨174809337112156848686209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 932316464598169859659781 174809337112156848686209)
            ·
              refine ⟨131107002834117636514657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 174809337112156848686209 131107002834117636514657)
              ·
                refine ⟨98330252125588227385993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131107002834117636514657 98330252125588227385993)
                ·
                  refine ⟨73747689094191170539495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98330252125588227385993 73747689094191170539495)
                  ·
                    rfl

theorem cell20_161576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 2].length) (baseStart_161576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161576 prefixEnd_161576 := by exact prefixLift 161576
  have htrace : WordTrace (prefixWord ++ tailWord_161576) baseStart_161576 baseEnd_161576 := by
    simpa [prefixWord, tailWord_161576, baseEnd_161576] using wordTrace_append hprefix tailTrace_161576
  have hstable : (prefixWord ++ tailWord_161576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161576).length < 2 ^ (prefixWord ++ tailWord_161576).sum := by decide
  have hdescent : baseEnd_161576 < baseStart_161576 := by decide
  rcases family_descends (prefixWord ++ tailWord_161576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161580 : List Nat := [2, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_161580 : Nat := 118140960795 + 161580 * 2 ^ 59
def prefixEnd_161580 : Nat := 4983230072969 + 3 ^ 40 * 161580 * 2
def baseEnd_161580 : Nat := 73749514803184934406145

theorem tailTrace_161580 : CollatzResearch.WordTrace tailWord_161580 prefixEnd_161580 73749514803184934406145 := by
  unfold tailWord_161580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2946653377315365256053097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3928871169753820341404129 2946653377315365256053097)
  ·
    refine ⟨2209990032986523942039823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2946653377315365256053097 2209990032986523942039823)
    ·
      refine ⟨3314985049479785913059735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2209990032986523942039823 3314985049479785913059735)
      ·
        refine ⟨4972477574219678869589603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3314985049479785913059735 4972477574219678869589603)
        ·
          refine ⟨7458716361329518304384405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4972477574219678869589603 7458716361329518304384405)
          ·
            refine ⟨349627329437321170518019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7458716361329518304384405 349627329437321170518019)
            ·
              refine ⟨524440994155981755777029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349627329437321170518019 524440994155981755777029)
              ·
                refine ⟨98332686404246579208193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 524440994155981755777029 98332686404246579208193)
                ·
                  refine ⟨73749514803184934406145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98332686404246579208193 73749514803184934406145)
                  ·
                    rfl

theorem cell20_161580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_161580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161580 prefixEnd_161580 := by exact prefixLift 161580
  have htrace : WordTrace (prefixWord ++ tailWord_161580) baseStart_161580 baseEnd_161580 := by
    simpa [prefixWord, tailWord_161580, baseEnd_161580] using wordTrace_append hprefix tailTrace_161580
  have hstable : (prefixWord ++ tailWord_161580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161580).length < 2 ^ (prefixWord ++ tailWord_161580).sum := by decide
  have hdescent : baseEnd_161580 < baseStart_161580 := by decide
  rcases family_descends (prefixWord ++ tailWord_161580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161587 : List Nat := [1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_161587 : Nat := 118140960795 + 161587 * 2 ^ 59
def prefixEnd_161587 : Nat := 4983230072969 + 3 ^ 40 * 161587 * 2
def baseEnd_161587 : Nat := 24584236597974673724261

theorem tailTrace_161587 : CollatzResearch.WordTrace tailWord_161587 prefixEnd_161587 24584236597974673724261 := by
  unfold tailWord_161587
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893562065605370707611015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3929041377070247138407343 5893562065605370707611015)
  ·
    refine ⟨8840343098408056061416523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893562065605370707611015 8840343098408056061416523)
    ·
      refine ⟨13260514647612084092124785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8840343098408056061416523 13260514647612084092124785)
      ·
        refine ⟨9945385985709063069093589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13260514647612084092124785 9945385985709063069093589)
        ·
          refine ⟨233094984040056165681881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9945385985709063069093589 233094984040056165681881)
          ·
            refine ⟨174821238030042124261411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233094984040056165681881 174821238030042124261411)
            ·
              refine ⟨262231857045063186392117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174821238030042124261411 262231857045063186392117)
              ·
                refine ⟨24584236597974673724261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262231857045063186392117 24584236597974673724261)
                ·
                  rfl

theorem cell20_161587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_161587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161587 prefixEnd_161587 := by exact prefixLift 161587
  have htrace : WordTrace (prefixWord ++ tailWord_161587) baseStart_161587 baseEnd_161587 := by
    simpa [prefixWord, tailWord_161587, baseEnd_161587] using wordTrace_append hprefix tailTrace_161587
  have hstable : (prefixWord ++ tailWord_161587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161587).length < 2 ^ (prefixWord ++ tailWord_161587).sum := by decide
  have hdescent : baseEnd_161587 < baseStart_161587 := by decide
  rcases family_descends (prefixWord ++ tailWord_161587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161591 : List Nat := [1, 1, 3, 1, 2, 1, 2, 9]
def baseStart_161591 : Nat := 118140960795 + 161591 * 2 ^ 59
def prefixEnd_161591 : Nat := 4983230072969 + 3 ^ 40 * 161591 * 2
def baseEnd_161591 : Nat := 24584845167639261679811

theorem tailTrace_161591 : CollatzResearch.WordTrace tailWord_161591 prefixEnd_161591 24584845167639261679811 := by
  unfold tailWord_161591
  simp only [CollatzResearch.WordTrace]
  refine ⟨5893707957590879390756627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3929138638393919593837751 5893707957590879390756627)
  ·
    refine ⟨8840561936386319086134941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5893707957590879390756627 8840561936386319086134941)
    ·
      refine ⟨3315210726144869657300603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8840561936386319086134941 3315210726144869657300603)
      ·
        refine ⟨4972816089217304485950905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315210726144869657300603 4972816089217304485950905)
        ·
          refine ⟨3729612066912978364463179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4972816089217304485950905 3729612066912978364463179)
          ·
            refine ⟨5594418100369467546694769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3729612066912978364463179 5594418100369467546694769)
            ·
              refine ⟨4195813575277100660021077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5594418100369467546694769 4195813575277100660021077)
              ·
                refine ⟨24584845167639261679811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4195813575277100660021077 24584845167639261679811)
                ·
                  rfl

theorem cell20_161591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 9].length) (baseStart_161591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161591 prefixEnd_161591 := by exact prefixLift 161591
  have htrace : WordTrace (prefixWord ++ tailWord_161591) baseStart_161591 baseEnd_161591 := by
    simpa [prefixWord, tailWord_161591, baseEnd_161591] using wordTrace_append hprefix tailTrace_161591
  have hstable : (prefixWord ++ tailWord_161591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161591).length < 2 ^ (prefixWord ++ tailWord_161591).sum := by decide
  have hdescent : baseEnd_161591 < baseStart_161591 := by decide
  rcases family_descends (prefixWord ++ tailWord_161591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161594 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 3]
def baseStart_161594 : Nat := 118140960795 + 161594 * 2 ^ 59
def prefixEnd_161594 : Nat := 4983230072969 + 3 ^ 40 * 161594 * 2
def baseEnd_161594 : Nat := 73755904784663107939421

theorem tailTrace_161594 : CollatzResearch.WordTrace tailWord_161594 prefixEnd_161594 73755904784663107939421 := by
  unfold tailWord_161594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473454344145002725778959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3929211584386673935410557 1473454344145002725778959)
  ·
    refine ⟨2210181516217504088668439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1473454344145002725778959 2210181516217504088668439)
    ·
      refine ⟨3315272274326256133002659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210181516217504088668439 3315272274326256133002659)
      ·
        refine ⟨4972908411489384199503989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3315272274326256133002659 4972908411489384199503989)
        ·
          refine ⟨466210163577129768703499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4972908411489384199503989 466210163577129768703499)
          ·
            refine ⟨699315245365694653055249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466210163577129768703499 699315245365694653055249)
            ·
              refine ⟨524486434024270989791437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 699315245365694653055249 524486434024270989791437)
              ·
                refine ⟨196682412759101621171789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524486434024270989791437 196682412759101621171789)
                ·
                  refine ⟨73755904784663107939421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196682412759101621171789 73755904784663107939421)
                  ·
                    rfl

theorem cell20_161594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 3].length) (baseStart_161594 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161594 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161594 prefixEnd_161594 := by exact prefixLift 161594
  have htrace : WordTrace (prefixWord ++ tailWord_161594) baseStart_161594 baseEnd_161594 := by
    simpa [prefixWord, tailWord_161594, baseEnd_161594] using wordTrace_append hprefix tailTrace_161594
  have hstable : (prefixWord ++ tailWord_161594).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161594).length < 2 ^ (prefixWord ++ tailWord_161594).sum := by decide
  have hdescent : baseEnd_161594 < baseStart_161594 := by decide
  rcases family_descends (prefixWord ++ tailWord_161594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161618 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 2]
def baseStart_161618 : Nat := 118140960795 + 161618 * 2 ^ 59
def prefixEnd_161618 : Nat := 4983230072969 + 3 ^ 40 * 161618 * 2
def baseEnd_161618 : Nat := 73766859038625691139323

theorem tailTrace_161618 : CollatzResearch.WordTrace tailWord_161618 prefixEnd_161618 73766859038625691139323 := by
  unfold tailWord_161618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1473673182123265750497377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3929795152328708667993005 1473673182123265750497377)
  ·
    refine ⟨1105254886592449312873033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1473673182123265750497377 1105254886592449312873033)
    ·
      refine ⟨828941164944336984654775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1105254886592449312873033 828941164944336984654775)
      ·
        refine ⟨1243411747416505476982163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 828941164944336984654775 1243411747416505476982163)
        ·
          refine ⟨1865117621124758215473245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1243411747416505476982163 1865117621124758215473245)
          ·
            refine ⟨699419107921784330802467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1865117621124758215473245 699419107921784330802467)
            ·
              refine ⟨1049128661882676496203701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 699419107921784330802467 1049128661882676496203701)
              ·
                refine ⟨98355812051500921519097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1049128661882676496203701 98355812051500921519097)
                ·
                  refine ⟨73766859038625691139323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98355812051500921519097 73766859038625691139323)
                  ·
                    rfl

theorem cell20_161618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_161618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161618 prefixEnd_161618 := by exact prefixLift 161618
  have htrace : WordTrace (prefixWord ++ tailWord_161618) baseStart_161618 baseEnd_161618 := by
    simpa [prefixWord, tailWord_161618, baseEnd_161618] using wordTrace_append hprefix tailTrace_161618
  have hstable : (prefixWord ++ tailWord_161618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161618).length < 2 ^ (prefixWord ++ tailWord_161618).sum := by decide
  have hdescent : baseEnd_161618 < baseStart_161618 := by decide
  rcases family_descends (prefixWord ++ tailWord_161618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161628 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_161628 : Nat := 118140960795 + 161628 * 2 ^ 59
def prefixEnd_161628 : Nat := 4983230072969 + 3 ^ 40 * 161628 * 2
def baseEnd_161628 : Nat := 73771423311110100805949

theorem tailTrace_161628 : CollatzResearch.WordTrace tailWord_161628 prefixEnd_161628 73771423311110100805949 := by
  unfold tailWord_161628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947528729228417354926769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3930038305637889806569025 2947528729228417354926769)
  ·
    refine ⟨2210646546921313016195077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2947528729228417354926769 2210646546921313016195077)
    ·
      refine ⟨414496227547746190536577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2210646546921313016195077 414496227547746190536577)
      ·
        refine ⟨310872170660809642902433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 414496227547746190536577 310872170660809642902433)
        ·
          refine ⟨233154127995607232176825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310872170660809642902433 233154127995607232176825)
          ·
            refine ⟨174865595996705424132619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233154127995607232176825 174865595996705424132619)
            ·
              refine ⟨262298393995058136198929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174865595996705424132619 262298393995058136198929)
              ·
                refine ⟨196723795496293602149197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262298393995058136198929 196723795496293602149197)
                ·
                  refine ⟨73771423311110100805949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196723795496293602149197 73771423311110100805949)
                  ·
                    rfl

theorem cell20_161628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_161628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161628 prefixEnd_161628 := by exact prefixLift 161628
  have htrace : WordTrace (prefixWord ++ tailWord_161628) baseStart_161628 baseEnd_161628 := by
    simpa [prefixWord, tailWord_161628, baseEnd_161628] using wordTrace_append hprefix tailTrace_161628
  have hstable : (prefixWord ++ tailWord_161628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161628).length < 2 ^ (prefixWord ++ tailWord_161628).sum := by decide
  have hdescent : baseEnd_161628 < baseStart_161628 := by decide
  rcases family_descends (prefixWord ++ tailWord_161628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161632 : List Nat := [2, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_161632 : Nat := 118140960795 + 161632 * 2 ^ 59
def prefixEnd_161632 : Nat := 4983230072969 + 3 ^ 40 * 161632 * 2
def baseEnd_161632 : Nat := 73773249020103864672599

theorem tailTrace_161632 : CollatzResearch.WordTrace tailWord_161632 prefixEnd_161632 73773249020103864672599 := by
  unfold tailWord_161632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947601675221171696499575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3930135566961562261999433 2947601675221171696499575)
  ·
    refine ⟨4421402512831757544749363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2947601675221171696499575 4421402512831757544749363)
    ·
      refine ⟨6632103769247636317124045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4421402512831757544749363 6632103769247636317124045)
      ·
        refine ⟨2487038913467863618921517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6632103769247636317124045 2487038913467863618921517)
        ·
          refine ⟨932639592550448857095569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2487038913467863618921517 932639592550448857095569)
          ·
            refine ⟨699479694412836642821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932639592550448857095569 699479694412836642821677)
            ·
              refine ⟨262304885404813741058129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 699479694412836642821677 262304885404813741058129)
              ·
                refine ⟨196728664053610305793597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 262304885404813741058129 196728664053610305793597)
                ·
                  refine ⟨73773249020103864672599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196728664053610305793597 73773249020103864672599)
                  ·
                    rfl

theorem cell20_161632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_161632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161632 prefixEnd_161632 := by exact prefixLift 161632
  have htrace : WordTrace (prefixWord ++ tailWord_161632) baseStart_161632 baseEnd_161632 := by
    simpa [prefixWord, tailWord_161632, baseEnd_161632] using wordTrace_append hprefix tailTrace_161632
  have hstable : (prefixWord ++ tailWord_161632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161632).length < 2 ^ (prefixWord ++ tailWord_161632).sum := by decide
  have hdescent : baseEnd_161632 < baseStart_161632 := by decide
  rcases family_descends (prefixWord ++ tailWord_161632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161639 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 4]
def baseStart_161639 : Nat := 118140960795 + 161639 * 2 ^ 59
def prefixEnd_161639 : Nat := 4983230072969 + 3 ^ 40 * 161639 * 2
def baseEnd_161639 : Nat := 73776444010842951439237

theorem tailTrace_161639 : CollatzResearch.WordTrace tailWord_161639 prefixEnd_161639 73776444010842951439237 := by
  unfold tailWord_161639
  simp only [CollatzResearch.WordTrace]
  refine ⟨5895458661416983588503971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3930305774277989059002647 5895458661416983588503971)
  ·
    refine ⟨8843187992125475382755957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5895458661416983588503971 8843187992125475382755957)
    ·
      refine ⟨829048874261763317133371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8843187992125475382755957 829048874261763317133371)
      ·
        refine ⟨1243573311392644975700057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 829048874261763317133371 1243573311392644975700057)
        ·
          refine ⟨932679983544483731775043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1243573311392644975700057 932679983544483731775043)
          ·
            refine ⟨1399019975316725597662565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 932679983544483731775043 1399019975316725597662565)
            ·
              refine ⟨262316245371886049561731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1399019975316725597662565 262316245371886049561731)
              ·
                refine ⟨393474368057829074342597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262316245371886049561731 393474368057829074342597)
                ·
                  refine ⟨73776444010842951439237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 393474368057829074342597 73776444010842951439237)
                  ·
                    rfl

theorem cell20_161639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 4].length) (baseStart_161639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161639 prefixEnd_161639 := by exact prefixLift 161639
  have htrace : WordTrace (prefixWord ++ tailWord_161639) baseStart_161639 baseEnd_161639 := by
    simpa [prefixWord, tailWord_161639, baseEnd_161639] using wordTrace_append hprefix tailTrace_161639
  have hstable : (prefixWord ++ tailWord_161639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161639).length < 2 ^ (prefixWord ++ tailWord_161639).sum := by decide
  have hdescent : baseEnd_161639 < baseStart_161639 := by decide
  rcases family_descends (prefixWord ++ tailWord_161639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161684 : List Nat := [2, 4, 2, 1, 1, 2, 8]
def baseStart_161684 : Nat := 118140960795 + 161684 * 2 ^ 59
def prefixEnd_161684 : Nat := 4983230072969 + 3 ^ 40 * 161684 * 2
def baseEnd_161684 : Nat := 8199664804113643882117

theorem tailTrace_161684 : CollatzResearch.WordTrace tailWord_161684 prefixEnd_161684 8199664804113643882117 := by
  unfold tailWord_161684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948549973126978136946053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3931399964169304182594737 2948549973126978136946053)
  ·
    refine ⟨552853119961308400677385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2948549973126978136946053 552853119961308400677385)
    ·
      refine ⟨414639839970981300508039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 552853119961308400677385 414639839970981300508039)
      ·
        refine ⟨621959759956471950762059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 414639839970981300508039 621959759956471950762059)
        ·
          refine ⟨932939639934707926143089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 621959759956471950762059 932939639934707926143089)
          ·
            refine ⟨699704729951030944607317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 932939639934707926143089 699704729951030944607317)
            ·
              refine ⟨8199664804113643882117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 699704729951030944607317 8199664804113643882117)
              ·
                rfl

theorem cell20_161684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 8].length) (baseStart_161684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161684 prefixEnd_161684 := by exact prefixLift 161684
  have htrace : WordTrace (prefixWord ++ tailWord_161684) baseStart_161684 baseEnd_161684 := by
    simpa [prefixWord, tailWord_161684, baseEnd_161684] using wordTrace_append hprefix tailTrace_161684
  have hstable : (prefixWord ++ tailWord_161684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161684).length < 2 ^ (prefixWord ++ tailWord_161684).sum := by decide
  have hdescent : baseEnd_161684 < baseStart_161684 := by decide
  rcases family_descends (prefixWord ++ tailWord_161684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161686 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_161686 : Nat := 118140960795 + 161686 * 2 ^ 59
def prefixEnd_161686 : Nat := 4983230072969 + 3 ^ 40 * 161686 * 2
def baseEnd_161686 : Nat := 73797896091519676872379

theorem tailTrace_161686 : CollatzResearch.WordTrace tailWord_161686 prefixEnd_161686 73797896091519676872379 := by
  unfold tailWord_161686
  simp only [CollatzResearch.WordTrace]
  refine ⟨368573305765419413466557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3931448594831140410309941 368573305765419413466557)
  ·
    refine ⟨138214989662032280049959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 368573305765419413466557 138214989662032280049959)
    ·
      refine ⟨207322484493048420074939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 138214989662032280049959 207322484493048420074939)
      ·
        refine ⟨310983726739572630112409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207322484493048420074939 310983726739572630112409)
        ·
          refine ⟨233237795054679472584307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 310983726739572630112409 233237795054679472584307)
          ·
            refine ⟨349856692582019208876461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233237795054679472584307 349856692582019208876461)
            ·
              refine ⟨131196259718257203328673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 349856692582019208876461 131196259718257203328673)
              ·
                refine ⟨98397194788692902496505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131196259718257203328673 98397194788692902496505)
                ·
                  refine ⟨73797896091519676872379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98397194788692902496505 73797896091519676872379)
                  ·
                    rfl

theorem cell20_161686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_161686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161686 prefixEnd_161686 := by exact prefixLift 161686
  have htrace : WordTrace (prefixWord ++ tailWord_161686) baseStart_161686 baseEnd_161686 := by
    simpa [prefixWord, tailWord_161686, baseEnd_161686] using wordTrace_append hprefix tailTrace_161686
  have hstable : (prefixWord ++ tailWord_161686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161686).length < 2 ^ (prefixWord ++ tailWord_161686).sum := by decide
  have hdescent : baseEnd_161686 < baseStart_161686 := by decide
  rcases family_descends (prefixWord ++ tailWord_161686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161704 : List Nat := [2, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_161704 : Nat := 118140960795 + 161704 * 2 ^ 59
def prefixEnd_161704 : Nat := 4983230072969 + 3 ^ 40 * 161704 * 2
def baseEnd_161704 : Nat := 73806111781991614272305

theorem tailTrace_161704 : CollatzResearch.WordTrace tailWord_161704 prefixEnd_161704 73806111781991614272305 := by
  unfold tailWord_161704
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948914703090749844810083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3931886270787666459746777 2948914703090749844810083)
  ·
    refine ⟨4423372054636124767215125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2948914703090749844810083 4423372054636124767215125)
    ·
      refine ⟨207345565061068348463209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4423372054636124767215125 207345565061068348463209)
      ·
        refine ⟨155509173795801261347407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207345565061068348463209 155509173795801261347407)
        ·
          refine ⟨233263760693701892021111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155509173795801261347407 233263760693701892021111)
          ·
            refine ⟨349895641040552838031667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233263760693701892021111 349895641040552838031667)
            ·
              refine ⟨524843461560829257047501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 349895641040552838031667 524843461560829257047501)
              ·
                refine ⟨196816298085310971392813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 524843461560829257047501 196816298085310971392813)
                ·
                  refine ⟨73806111781991614272305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 196816298085310971392813 73806111781991614272305)
                  ·
                    rfl

theorem cell20_161704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_161704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161704 prefixEnd_161704 := by exact prefixLift 161704
  have htrace : WordTrace (prefixWord ++ tailWord_161704) baseStart_161704 baseEnd_161704 := by
    simpa [prefixWord, tailWord_161704, baseEnd_161704] using wordTrace_append hprefix tailTrace_161704
  have hstable : (prefixWord ++ tailWord_161704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161704).length < 2 ^ (prefixWord ++ tailWord_161704).sum := by decide
  have hdescent : baseEnd_161704 < baseStart_161704 := by decide
  rcases family_descends (prefixWord ++ tailWord_161704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161749 : List Nat := [1, 3, 2, 3, 2, 1, 4, 2, 2]
def baseStart_161749 : Nat := 118140960795 + 161749 * 2 ^ 59
def prefixEnd_161749 : Nat := 4983230072969 + 3 ^ 40 * 161749 * 2
def baseEnd_161749 : Nat := 73826651008171457772121

theorem tailTrace_161749 : CollatzResearch.WordTrace tailWord_161749 prefixEnd_161749 73826651008171457772121 := by
  unfold tailWord_161749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5899470691018472375008301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3932980460678981583338867 5899470691018472375008301)
  ·
    refine ⟨2212301509131927140628113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5899470691018472375008301 2212301509131927140628113)
    ·
      refine ⟨1659226131848945355471085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212301509131927140628113 1659226131848945355471085)
      ·
        refine ⟨622209799443354508301657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1659226131848945355471085 622209799443354508301657)
        ·
          refine ⟨466657349582515881226243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 622209799443354508301657 466657349582515881226243)
          ·
            refine ⟨699986024373773821839365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 466657349582515881226243 699986024373773821839365)
            ·
              refine ⟨131247379570082591594881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 699986024373773821839365 131247379570082591594881)
              ·
                refine ⟨98435534677561943696161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131247379570082591594881 98435534677561943696161)
                ·
                  refine ⟨73826651008171457772121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98435534677561943696161 73826651008171457772121)
                  ·
                    rfl

theorem cell20_161749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_161749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161749 prefixEnd_161749 := by exact prefixLift 161749
  have htrace : WordTrace (prefixWord ++ tailWord_161749) baseStart_161749 baseEnd_161749 := by
    simpa [prefixWord, tailWord_161749, baseEnd_161749] using wordTrace_append hprefix tailTrace_161749
  have hstable : (prefixWord ++ tailWord_161749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161749).length < 2 ^ (prefixWord ++ tailWord_161749).sum := by decide
  have hdescent : baseEnd_161749 < baseStart_161749 := by decide
  rcases family_descends (prefixWord ++ tailWord_161749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161777 : List Nat := [1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_161777 : Nat := 118140960795 + 161777 * 2 ^ 59
def prefixEnd_161777 : Nat := 4983230072969 + 3 ^ 40 * 161777 * 2
def baseEnd_161777 : Nat := 24613143657042601612891

theorem tailTrace_161777 : CollatzResearch.WordTrace tailWord_161777 prefixEnd_161777 24613143657042601612891 := by
  unfold tailWord_161777
  simp only [CollatzResearch.WordTrace]
  refine ⟨5900491934917033157027585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3933661289944688771351723 5900491934917033157027585)
  ·
    refine ⟨4425368951187774867770689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5900491934917033157027585 4425368951187774867770689)
    ·
      refine ⟨3319026713390831150828017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4425368951187774867770689 3319026713390831150828017)
      ·
        refine ⟨2489270035043123363121013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3319026713390831150828017 2489270035043123363121013)
        ·
          refine ⟨233369065785292815292595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2489270035043123363121013 233369065785292815292595)
          ·
            refine ⟨350053598677939222938893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233369065785292815292595 350053598677939222938893)
            ·
              refine ⟨131270099504227208602085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350053598677939222938893 131270099504227208602085)
              ·
                refine ⟨24613143657042601612891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131270099504227208602085 24613143657042601612891)
                ·
                  rfl

theorem cell20_161777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_161777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161777 prefixEnd_161777 := by exact prefixLift 161777
  have htrace : WordTrace (prefixWord ++ tailWord_161777) baseStart_161777 baseEnd_161777 := by
    simpa [prefixWord, tailWord_161777, baseEnd_161777] using wordTrace_append hprefix tailTrace_161777
  have hstable : (prefixWord ++ tailWord_161777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161777).length < 2 ^ (prefixWord ++ tailWord_161777).sum := by decide
  have hdescent : baseEnd_161777 < baseStart_161777 := by decide
  rcases family_descends (prefixWord ++ tailWord_161777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161877 : List Nat := [1, 3, 2, 2, 1, 5, 2, 1, 3]
def baseStart_161877 : Nat := 118140960795 + 161877 * 2 ^ 59
def prefixEnd_161877 : Nat := 4983230072969 + 3 ^ 40 * 161877 * 2
def baseEnd_161877 : Nat := 73885073695971901504931

theorem tailTrace_161877 : CollatzResearch.WordTrace tailWord_161877 prefixEnd_161877 73885073695971901504931 := by
  unfold tailWord_161877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904139234554750235667885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936092823036500157111923 5904139234554750235667885)
  ·
    refine ⟨2214052212958031338375457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5904139234554750235667885 2214052212958031338375457)
    ·
      refine ⟨1660539159718523503781593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2214052212958031338375457 1660539159718523503781593)
      ·
        refine ⟨1245404369788892627836195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1660539159718523503781593 1245404369788892627836195)
        ·
          refine ⟨1868106554683338941754293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245404369788892627836195 1868106554683338941754293)
          ·
            refine ⟨175134989501563025789465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1868106554683338941754293 175134989501563025789465)
            ·
              refine ⟨131351242126172269342099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175134989501563025789465 131351242126172269342099)
              ·
                refine ⟨197026863189258404013149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131351242126172269342099 197026863189258404013149)
                ·
                  refine ⟨73885073695971901504931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197026863189258404013149 73885073695971901504931)
                  ·
                    rfl

theorem cell20_161877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_161877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161877 prefixEnd_161877 := by exact prefixLift 161877
  have htrace : WordTrace (prefixWord ++ tailWord_161877) baseStart_161877 baseEnd_161877 := by
    simpa [prefixWord, tailWord_161877, baseEnd_161877] using wordTrace_append hprefix tailTrace_161877
  have hstable : (prefixWord ++ tailWord_161877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161877).length < 2 ^ (prefixWord ++ tailWord_161877).sum := by decide
  have hdescent : baseEnd_161877 < baseStart_161877 := by decide
  rcases family_descends (prefixWord ++ tailWord_161877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161881 : List Nat := [1, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_161881 : Nat := 118140960795 + 161881 * 2 ^ 59
def prefixEnd_161881 : Nat := 4983230072969 + 3 ^ 40 * 161881 * 2
def baseEnd_161881 : Nat := 73886899404965665371581

theorem tailTrace_161881 : CollatzResearch.WordTrace tailWord_161881 prefixEnd_161881 73886899404965665371581 := by
  unfold tailWord_161881
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904285126540258918813497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936190084360172612542331 5904285126540258918813497)
  ·
    refine ⟨4428213844905194189110123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5904285126540258918813497 4428213844905194189110123)
    ·
      refine ⟨6642320767357791283665185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4428213844905194189110123 6642320767357791283665185)
      ·
        refine ⟨4981740575518343462748889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6642320767357791283665185 4981740575518343462748889)
        ·
          refine ⟨3736305431638757597061667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4981740575518343462748889 3736305431638757597061667)
          ·
            refine ⟨5604458147458136395592501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736305431638757597061667 5604458147458136395592501)
            ·
              refine ⟨525417951324200287086797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5604458147458136395592501 525417951324200287086797)
              ·
                refine ⟨197031731746575107657549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 525417951324200287086797 197031731746575107657549)
                ·
                  refine ⟨73886899404965665371581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197031731746575107657549 73886899404965665371581)
                  ·
                    rfl

theorem cell20_161881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_161881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161881 prefixEnd_161881 := by exact prefixLift 161881
  have htrace : WordTrace (prefixWord ++ tailWord_161881) baseStart_161881 baseEnd_161881 := by
    simpa [prefixWord, tailWord_161881, baseEnd_161881] using wordTrace_append hprefix tailTrace_161881
  have hstable : (prefixWord ++ tailWord_161881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161881).length < 2 ^ (prefixWord ++ tailWord_161881).sum := by decide
  have hdescent : baseEnd_161881 < baseStart_161881 := by decide
  rcases family_descends (prefixWord ++ tailWord_161881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161895 : List Nat := [1, 1, 5, 1, 1, 2, 1, 8]
def baseStart_161895 : Nat := 118140960795 + 161895 * 2 ^ 59
def prefixEnd_161895 : Nat := 4983230072969 + 3 ^ 40 * 161895 * 2
def baseEnd_161895 : Nat := 24631096462147946301619

theorem tailTrace_161895 : CollatzResearch.WordTrace tailWord_161895 prefixEnd_161895 24631096462147946301619 := by
  unfold tailWord_161895
  simp only [CollatzResearch.WordTrace]
  refine ⟨5904795748489539309823139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936530498993026206548759 5904795748489539309823139)
  ·
    refine ⟨8857193622734308964734709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5904795748489539309823139 8857193622734308964734709)
    ·
      refine ⟨830361902131341465443879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8857193622734308964734709 830361902131341465443879)
      ·
        refine ⟨1245542853197012198165819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 830361902131341465443879 1245542853197012198165819)
        ·
          refine ⟨1868314279795518297248729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1245542853197012198165819 1868314279795518297248729)
          ·
            refine ⟨1401235709846638722936547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1868314279795518297248729 1401235709846638722936547)
            ·
              refine ⟨2101853564769958084404821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1401235709846638722936547 2101853564769958084404821)
              ·
                refine ⟨24631096462147946301619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2101853564769958084404821 24631096462147946301619)
                ·
                  rfl

theorem cell20_161895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 8].length) (baseStart_161895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161895 prefixEnd_161895 := by exact prefixLift 161895
  have htrace : WordTrace (prefixWord ++ tailWord_161895) baseStart_161895 baseEnd_161895 := by
    simpa [prefixWord, tailWord_161895, baseEnd_161895] using wordTrace_append hprefix tailTrace_161895
  have hstable : (prefixWord ++ tailWord_161895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161895).length < 2 ^ (prefixWord ++ tailWord_161895).sum := by decide
  have hdescent : baseEnd_161895 < baseStart_161895 := by decide
  rcases family_descends (prefixWord ++ tailWord_161895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161905 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 2]
def baseStart_161905 : Nat := 118140960795 + 161905 * 2 ^ 59
def prefixEnd_161905 : Nat := 4983230072969 + 3 ^ 40 * 161905 * 2
def baseEnd_161905 : Nat := 73897853658928248571483

theorem tailTrace_161905 : CollatzResearch.WordTrace tailWord_161905 prefixEnd_161905 73897853658928248571483 := by
  unfold tailWord_161905
  simp only [CollatzResearch.WordTrace]
  refine ⟨5905160478453311017687169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3936773652302207345124779 5905160478453311017687169)
  ·
    refine ⟨4428870358839983263265377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5905160478453311017687169 4428870358839983263265377)
    ·
      refine ⟨3321652769129987447449033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4428870358839983263265377 3321652769129987447449033)
      ·
        refine ⟨2491239576847490585586775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3321652769129987447449033 2491239576847490585586775)
        ·
          refine ⟨3736859365271235878380163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2491239576847490585586775 3736859365271235878380163)
          ·
            refine ⟨5605289047906853817570245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3736859365271235878380163 5605289047906853817570245)
            ·
              refine ⟨1050991696482535090794421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5605289047906853817570245 1050991696482535090794421)
              ·
                refine ⟨98530471545237664761977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1050991696482535090794421 98530471545237664761977)
                ·
                  refine ⟨73897853658928248571483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98530471545237664761977 73897853658928248571483)
                  ·
                    rfl

theorem cell20_161905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 2].length) (baseStart_161905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161905 prefixEnd_161905 := by exact prefixLift 161905
  have htrace : WordTrace (prefixWord ++ tailWord_161905) baseStart_161905 baseEnd_161905 := by
    simpa [prefixWord, tailWord_161905, baseEnd_161905] using wordTrace_append hprefix tailTrace_161905
  have hstable : (prefixWord ++ tailWord_161905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161905).length < 2 ^ (prefixWord ++ tailWord_161905).sum := by decide
  have hdescent : baseEnd_161905 < baseStart_161905 := by decide
  rcases family_descends (prefixWord ++ tailWord_161905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_161943 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_161943 : Nat := 118140960795 + 161943 * 2 ^ 59
def prefixEnd_161943 : Nat := 4983230072969 + 3 ^ 40 * 161943 * 2
def baseEnd_161943 : Nat := 73915197894369005304661

theorem tailTrace_161943 : CollatzResearch.WordTrace tailWord_161943 prefixEnd_161943 73915197894369005304661 := by
  unfold tailWord_161943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5906546452315643507570483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3937697634877095671713655 5906546452315643507570483)
  ·
    refine ⟨8859819678473465261355725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5906546452315643507570483 8859819678473465261355725)
    ·
      refine ⟨3322432379427549473008397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8859819678473465261355725 3322432379427549473008397)
      ·
        refine ⟨1245912142285331052378149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3322432379427549473008397 1245912142285331052378149)
        ·
          refine ⟨233608526678499572320903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1245912142285331052378149 233608526678499572320903)
          ·
            refine ⟨350412790017749358481355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233608526678499572320903 350412790017749358481355)
            ·
              refine ⟨525619185026624037722033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350412790017749358481355 525619185026624037722033)
              ·
                refine ⟨394214388769968028291525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525619185026624037722033 394214388769968028291525)
                ·
                  refine ⟨73915197894369005304661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 394214388769968028291525 73915197894369005304661)
                  ·
                    rfl

theorem cell20_161943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_161943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_161943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_161943 prefixEnd_161943 := by exact prefixLift 161943
  have htrace : WordTrace (prefixWord ++ tailWord_161943) baseStart_161943 baseEnd_161943 := by
    simpa [prefixWord, tailWord_161943, baseEnd_161943] using wordTrace_append hprefix tailTrace_161943
  have hstable : (prefixWord ++ tailWord_161943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_161943).length < 2 ^ (prefixWord ++ tailWord_161943).sum := by decide
  have hdescent : baseEnd_161943 < baseStart_161943 := by decide
  rcases family_descends (prefixWord ++ tailWord_161943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162016 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_162016 : Nat := 118140960795 + 162016 * 2 ^ 59
def prefixEnd_162016 : Nat := 4983230072969 + 3 ^ 40 * 162016 * 2
def baseEnd_162016 : Nat := 73948517083505195871029

theorem tailTrace_162016 : CollatzResearch.WordTrace tailWord_162016 prefixEnd_162016 73948517083505195871029 := by
  unfold tailWord_162016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2954604490525588487488951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3939472654034117983318601 2954604490525588487488951)
  ·
    refine ⟨4431906735788382731233427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2954604490525588487488951 4431906735788382731233427)
    ·
      refine ⟨6647860103682574096850141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4431906735788382731233427 6647860103682574096850141)
      ·
        refine ⟨2492947538880965286318803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6647860103682574096850141 2492947538880965286318803)
        ·
          refine ⟨3739421308321447929478205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492947538880965286318803 3739421308321447929478205)
          ·
            refine ⟨1402282990620542973554327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3739421308321447929478205 1402282990620542973554327)
            ·
              refine ⟨2103424485930814460331491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402282990620542973554327 2103424485930814460331491)
              ·
                refine ⟨3155136728896221690497237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2103424485930814460331491 3155136728896221690497237)
                ·
                  refine ⟨73948517083505195871029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3155136728896221690497237 73948517083505195871029)
                  ·
                    rfl

theorem cell20_162016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_162016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162016 prefixEnd_162016 := by exact prefixLift 162016
  have htrace : WordTrace (prefixWord ++ tailWord_162016) baseStart_162016 baseEnd_162016 := by
    simpa [prefixWord, tailWord_162016, baseEnd_162016] using wordTrace_append hprefix tailTrace_162016
  have hstable : (prefixWord ++ tailWord_162016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162016).length < 2 ^ (prefixWord ++ tailWord_162016).sum := by decide
  have hdescent : baseEnd_162016 < baseStart_162016 := by decide
  rcases family_descends (prefixWord ++ tailWord_162016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162047 : List Nat := [1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_162047 : Nat := 118140960795 + 162047 * 2 ^ 59
def prefixEnd_162047 : Nat := 4983230072969 + 3 ^ 40 * 162047 * 2
def baseEnd_162047 : Nat := 24654222109402288612523

theorem tailTrace_162047 : CollatzResearch.WordTrace tailWord_162047 prefixEnd_162047 24654222109402288612523 := by
  unfold tailWord_162047
  simp only [CollatzResearch.WordTrace]
  refine ⟨5910339643938869269356395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3940226429292579512904263 5910339643938869269356395)
  ·
    refine ⟨8865509465908303904034593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5910339643938869269356395 8865509465908303904034593)
    ·
      refine ⟨6649132099431227928025945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8865509465908303904034593 6649132099431227928025945)
      ·
        refine ⟨4986849074573420946019459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6649132099431227928025945 4986849074573420946019459)
        ·
          refine ⟨7480273611860131419029189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4986849074573420946019459 7480273611860131419029189)
          ·
            refine ⟨1402551302223774641067973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7480273611860131419029189 1402551302223774641067973)
            ·
              refine ⟨262978369166957745200245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1402551302223774641067973 262978369166957745200245)
              ·
                refine ⟨24654222109402288612523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 262978369166957745200245 24654222109402288612523)
                ·
                  rfl

theorem cell20_162047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_162047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162047 prefixEnd_162047 := by exact prefixLift 162047
  have htrace : WordTrace (prefixWord ++ tailWord_162047) baseStart_162047 baseEnd_162047 := by
    simpa [prefixWord, tailWord_162047, baseEnd_162047] using wordTrace_append hprefix tailTrace_162047
  have hstable : (prefixWord ++ tailWord_162047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162047).length < 2 ^ (prefixWord ++ tailWord_162047).sum := by decide
  have hdescent : baseEnd_162047 < baseStart_162047 := by decide
  rcases family_descends (prefixWord ++ tailWord_162047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162085 : List Nat := [1, 3, 1, 2, 5, 8]
def baseStart_162085 : Nat := 118140960795 + 162085 * 2 ^ 59
def prefixEnd_162085 : Nat := 4983230072969 + 3 ^ 40 * 162085 * 2
def baseEnd_162085 : Nat := 2740000391246208243361

theorem tailTrace_162085 : CollatzResearch.WordTrace tailWord_162085 prefixEnd_162085 2740000391246208243361 := by
  unfold tailWord_162085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5911725617801201759239709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3941150411867467839493139 5911725617801201759239709)
  ·
    refine ⟨2216897106675450659714891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5911725617801201759239709 2216897106675450659714891)
    ·
      refine ⟨3325345660013175989572337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216897106675450659714891 3325345660013175989572337)
      ·
        refine ⟨2494009245009881992179253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3325345660013175989572337 2494009245009881992179253)
        ·
          refine ⟨233813366719676436766805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2494009245009881992179253 233813366719676436766805)
          ·
            refine ⟨2740000391246208243361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 233813366719676436766805 2740000391246208243361)
            ·
              rfl

theorem cell20_162085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 8].length) (baseStart_162085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162085 prefixEnd_162085 := by exact prefixLift 162085
  have htrace : WordTrace (prefixWord ++ tailWord_162085) baseStart_162085 baseEnd_162085 := by
    simpa [prefixWord, tailWord_162085, baseEnd_162085] using wordTrace_append hprefix tailTrace_162085
  have hstable : (prefixWord ++ tailWord_162085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162085).length < 2 ^ (prefixWord ++ tailWord_162085).sum := by decide
  have hdescent : baseEnd_162085 < baseStart_162085 := by decide
  rcases family_descends (prefixWord ++ tailWord_162085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162092 : List Nat := [2, 2, 1, 1, 1, 3, 2, 3, 5]
def baseStart_162092 : Nat := 118140960795 + 162092 * 2 ^ 59
def prefixEnd_162092 : Nat := 4983230072969 + 3 ^ 40 * 162092 * 2
def baseEnd_162092 : Nat := 73983205554386709337385

theorem tailTrace_162092 : CollatzResearch.WordTrace tailWord_162092 prefixEnd_162092 73983205554386709337385 := by
  unfold tailWord_162092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955990464387920977372265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3941320619183894636496353 2955990464387920977372265)
  ·
    refine ⟨2216992848290940733029199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2955990464387920977372265 2216992848290940733029199)
    ·
      refine ⟨3325489272436411099543799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216992848290940733029199 3325489272436411099543799)
      ·
        refine ⟨4988233908654616649315699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3325489272436411099543799 4988233908654616649315699)
        ·
          refine ⟨7482350862981924973973549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988233908654616649315699 7482350862981924973973549)
          ·
            refine ⟨2805881573618221865240081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7482350862981924973973549 2805881573618221865240081)
            ·
              refine ⟨2104411180213666398930061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2805881573618221865240081 2104411180213666398930061)
              ·
                refine ⟨789154192580124899598773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2104411180213666398930061 789154192580124899598773)
                ·
                  refine ⟨73983205554386709337385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 789154192580124899598773 73983205554386709337385)
                  ·
                    rfl

theorem cell20_162092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_162092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162092 prefixEnd_162092 := by exact prefixLift 162092
  have htrace : WordTrace (prefixWord ++ tailWord_162092) baseStart_162092 baseEnd_162092 := by
    simpa [prefixWord, tailWord_162092, baseEnd_162092] using wordTrace_append hprefix tailTrace_162092
  have hstable : (prefixWord ++ tailWord_162092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162092).length < 2 ^ (prefixWord ++ tailWord_162092).sum := by decide
  have hdescent : baseEnd_162092 < baseStart_162092 := by decide
  rcases family_descends (prefixWord ++ tailWord_162092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162137 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 8]
def baseStart_162137 : Nat := 118140960795 + 162137 * 2 ^ 59
def prefixEnd_162137 : Nat := 4983230072969 + 3 ^ 40 * 162137 * 2
def baseEnd_162137 : Nat := 74003744780566552837201

theorem tailTrace_162137 : CollatzResearch.WordTrace tailWord_162137 prefixEnd_162137 74003744780566552837201 := by
  unfold tailWord_162137
  simp only [CollatzResearch.WordTrace]
  refine ⟨5913622213612814640132665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3942414809075209760088443 5913622213612814640132665)
  ·
    refine ⟨4435216660209610980099499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5913622213612814640132665 4435216660209610980099499)
    ·
      refine ⟨6652824990314416470149249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4435216660209610980099499 6652824990314416470149249)
      ·
        refine ⟨4989618742735812352611937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6652824990314416470149249 4989618742735812352611937)
        ·
          refine ⟨3742214057051859264458953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4989618742735812352611937 3742214057051859264458953)
          ·
            refine ⟨2806660542788894448344215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742214057051859264458953 2806660542788894448344215)
            ·
              refine ⟨4209990814183341672516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806660542788894448344215 4209990814183341672516323)
              ·
                refine ⟨6314986221275012508774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209990814183341672516323 6314986221275012508774485)
                ·
                  refine ⟨74003744780566552837201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6314986221275012508774485 74003744780566552837201)
                  ·
                    rfl

theorem cell20_162137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_162137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162137 prefixEnd_162137 := by exact prefixLift 162137
  have htrace : WordTrace (prefixWord ++ tailWord_162137) baseStart_162137 baseEnd_162137 := by
    simpa [prefixWord, tailWord_162137, baseEnd_162137] using wordTrace_append hprefix tailTrace_162137
  have hstable : (prefixWord ++ tailWord_162137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162137).length < 2 ^ (prefixWord ++ tailWord_162137).sum := by decide
  have hdescent : baseEnd_162137 < baseStart_162137 := by decide
  rcases family_descends (prefixWord ++ tailWord_162137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162188 : List Nat := [2, 2, 1, 2, 1, 6, 1, 3, 2]
def baseStart_162188 : Nat := 118140960795 + 162188 * 2 ^ 59
def prefixEnd_162188 : Nat := 4983230072969 + 3 ^ 40 * 162188 * 2
def baseEnd_162188 : Nat := 74027022570237042136993

theorem tailTrace_162188 : CollatzResearch.WordTrace tailWord_162188 prefixEnd_162188 74027022570237042136993 := by
  unfold tailWord_162188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2957741168214025175119609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3943654890952033566826145 2957741168214025175119609)
  ·
    refine ⟨2218305876160518881339707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2957741168214025175119609 2218305876160518881339707)
    ·
      refine ⟨3327458814240778322009561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218305876160518881339707 3327458814240778322009561)
      ·
        refine ⟨2495594110680583741507171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3327458814240778322009561 2495594110680583741507171)
        ·
          refine ⟨3743391166020875612260757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495594110680583741507171 3743391166020875612260757)
          ·
            refine ⟨175471460907228544324723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3743391166020875612260757 175471460907228544324723)
            ·
              refine ⟨263207191360842816487085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175471460907228544324723 263207191360842816487085)
              ·
                refine ⟨98702696760316056182657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263207191360842816487085 98702696760316056182657)
                ·
                  refine ⟨74027022570237042136993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98702696760316056182657 74027022570237042136993)
                  ·
                    rfl

theorem cell20_162188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_162188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162188 prefixEnd_162188 := by exact prefixLift 162188
  have htrace : WordTrace (prefixWord ++ tailWord_162188) baseStart_162188 baseEnd_162188 := by
    simpa [prefixWord, tailWord_162188, baseEnd_162188] using wordTrace_append hprefix tailTrace_162188
  have hstable : (prefixWord ++ tailWord_162188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162188).length < 2 ^ (prefixWord ++ tailWord_162188).sum := by decide
  have hdescent : baseEnd_162188 < baseStart_162188 := by decide
  rcases family_descends (prefixWord ++ tailWord_162188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162205 : List Nat := [1, 4, 2, 1, 4, 1, 3, 2, 2]
def baseStart_162205 : Nat := 118140960795 + 162205 * 2 ^ 59
def prefixEnd_162205 : Nat := 4983230072969 + 3 ^ 40 * 162205 * 2
def baseEnd_162205 : Nat := 74034781833460538570257

theorem tailTrace_162205 : CollatzResearch.WordTrace tailWord_162205 prefixEnd_162205 74034781833460538570257 := by
  unfold tailWord_162205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916102377366462253608069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3944068251577641502405379 5916102377366462253608069)
  ·
    refine ⟨1109269195756211672551513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5916102377366462253608069 1109269195756211672551513)
    ·
      refine ⟨831951896817158754413635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109269195756211672551513 831951896817158754413635)
      ·
        refine ⟨1247927845225738131620453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831951896817158754413635 1247927845225738131620453)
        ·
          refine ⟨233986470979825899678835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1247927845225738131620453 233986470979825899678835)
          ·
            refine ⟨350979706469738849518253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233986470979825899678835 350979706469738849518253)
            ·
              refine ⟨131617389926152068569345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350979706469738849518253 131617389926152068569345)
              ·
                refine ⟨98713042444614051427009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131617389926152068569345 98713042444614051427009)
                ·
                  refine ⟨74034781833460538570257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98713042444614051427009 74034781833460538570257)
                  ·
                    rfl

theorem cell20_162205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_162205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162205 prefixEnd_162205 := by exact prefixLift 162205
  have htrace : WordTrace (prefixWord ++ tailWord_162205) baseStart_162205 baseEnd_162205 := by
    simpa [prefixWord, tailWord_162205, baseEnd_162205] using wordTrace_append hprefix tailTrace_162205
  have hstable : (prefixWord ++ tailWord_162205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162205).length < 2 ^ (prefixWord ++ tailWord_162205).sum := by decide
  have hdescent : baseEnd_162205 < baseStart_162205 := by decide
  rcases family_descends (prefixWord ++ tailWord_162205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162216 : List Nat := [2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_162216 : Nat := 118140960795 + 162216 * 2 ^ 59
def prefixEnd_162216 : Nat := 4983230072969 + 3 ^ 40 * 162216 * 2
def baseEnd_162216 : Nat := 24679934177731129734515

theorem tailTrace_162216 : CollatzResearch.WordTrace tailWord_162216 prefixEnd_162216 24679934177731129734515 := by
  unfold tailWord_162216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958251790163305566129251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3944335720217740754839001 2958251790163305566129251)
  ·
    refine ⟨4437377685244958349193877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2958251790163305566129251 4437377685244958349193877)
    ·
      refine ⟨208002078995857422618463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4437377685244958349193877 208002078995857422618463)
      ·
        refine ⟨312003118493786133927695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208002078995857422618463 312003118493786133927695)
        ·
          refine ⟨468004677740679200891543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312003118493786133927695 468004677740679200891543)
          ·
            refine ⟨702007016611018801337315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 468004677740679200891543 702007016611018801337315)
            ·
              refine ⟨1053010524916528202005973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702007016611018801337315 1053010524916528202005973)
              ·
                refine ⟨24679934177731129734515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1053010524916528202005973 24679934177731129734515)
                ·
                  rfl

theorem cell20_162216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_162216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162216 prefixEnd_162216 := by exact prefixLift 162216
  have htrace : WordTrace (prefixWord ++ tailWord_162216) baseStart_162216 baseEnd_162216 := by
    simpa [prefixWord, tailWord_162216, baseEnd_162216] using wordTrace_append hprefix tailTrace_162216
  have hstable : (prefixWord ++ tailWord_162216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162216).length < 2 ^ (prefixWord ++ tailWord_162216).sum := by decide
  have hdescent : baseEnd_162216 < baseStart_162216 := by decide
  rcases family_descends (prefixWord ++ tailWord_162216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162237 : List Nat := [1, 4, 1, 2, 2, 2, 2, 6]
def baseStart_162237 : Nat := 118140960795 + 162237 * 2 ^ 59
def prefixEnd_162237 : Nat := 4983230072969 + 3 ^ 40 * 162237 * 2
def baseEnd_162237 : Nat := 24683129168470216501153

theorem tailTrace_162237 : CollatzResearch.WordTrace tailWord_162237 prefixEnd_162237 24683129168470216501153 := by
  unfold tailWord_162237
  simp only [CollatzResearch.WordTrace]
  refine ⟨5917269513250531718772965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3944846342167021145848643 5917269513250531718772965)
  ·
    refine ⟨1109488033734474697269931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5917269513250531718772965 1109488033734474697269931)
    ·
      refine ⟨1664232050601712045904897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1109488033734474697269931 1664232050601712045904897)
      ·
        refine ⟨1248174037951284034428673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664232050601712045904897 1248174037951284034428673)
        ·
          refine ⟨936130528463463025821505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248174037951284034428673 936130528463463025821505)
          ·
            refine ⟨702097896347597269366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936130528463463025821505 702097896347597269366129)
            ·
              refine ⟨526573422260697952024597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 702097896347597269366129 526573422260697952024597)
              ·
                refine ⟨24683129168470216501153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 526573422260697952024597 24683129168470216501153)
                ·
                  rfl

theorem cell20_162237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 6].length) (baseStart_162237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162237 prefixEnd_162237 := by exact prefixLift 162237
  have htrace : WordTrace (prefixWord ++ tailWord_162237) baseStart_162237 baseEnd_162237 := by
    simpa [prefixWord, tailWord_162237, baseEnd_162237] using wordTrace_append hprefix tailTrace_162237
  have hstable : (prefixWord ++ tailWord_162237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162237).length < 2 ^ (prefixWord ++ tailWord_162237).sum := by decide
  have hdescent : baseEnd_162237 < baseStart_162237 := by decide
  rcases family_descends (prefixWord ++ tailWord_162237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162261 : List Nat := [1, 3, 2, 3, 1, 2, 1, 4, 3]
def baseStart_162261 : Nat := 118140960795 + 162261 * 2 ^ 59
def prefixEnd_162261 : Nat := 4983230072969 + 3 ^ 40 * 162261 * 2
def baseEnd_162261 : Nat := 74060341759373232703361

theorem tailTrace_162261 : CollatzResearch.WordTrace tailWord_162261 prefixEnd_162261 74060341759373232703361 := by
  unfold tailWord_162261
  simp only [CollatzResearch.WordTrace]
  refine ⟨5918144865163583817646637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3945429910109055878431091 5918144865163583817646637)
  ·
    refine ⟨2219304324436343931617489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5918144865163583817646637 2219304324436343931617489)
    ·
      refine ⟨1664478243327257948713117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219304324436343931617489 1664478243327257948713117)
      ·
        refine ⟨624179341247721730767419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1664478243327257948713117 624179341247721730767419)
        ·
          refine ⟨936269011871582596151129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 624179341247721730767419 936269011871582596151129)
          ·
            refine ⟨702201758903686947113347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 936269011871582596151129 702201758903686947113347)
            ·
              refine ⟨1053302638355530420670021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 702201758903686947113347 1053302638355530420670021)
              ·
                refine ⟨197494244691661953875629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1053302638355530420670021 197494244691661953875629)
                ·
                  refine ⟨74060341759373232703361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197494244691661953875629 74060341759373232703361)
                  ·
                    rfl

theorem cell20_162261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_162261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162261 prefixEnd_162261 := by exact prefixLift 162261
  have htrace : WordTrace (prefixWord ++ tailWord_162261) baseStart_162261 baseEnd_162261 := by
    simpa [prefixWord, tailWord_162261, baseEnd_162261] using wordTrace_append hprefix tailTrace_162261
  have hstable : (prefixWord ++ tailWord_162261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162261).length < 2 ^ (prefixWord ++ tailWord_162261).sum := by decide
  have hdescent : baseEnd_162261 < baseStart_162261 := by decide
  rcases family_descends (prefixWord ++ tailWord_162261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162285 : List Nat := [1, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_162285 : Nat := 118140960795 + 162285 * 2 ^ 59
def prefixEnd_162285 : Nat := 4983230072969 + 3 ^ 40 * 162285 * 2
def baseEnd_162285 : Nat := 74071296013335815903263

theorem tailTrace_162285 : CollatzResearch.WordTrace tailWord_162285 prefixEnd_162285 74071296013335815903263 := by
  unfold tailWord_162285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5919020217076635916520309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3946013478051090611013539 5919020217076635916520309)
  ·
    refine ⟨554908145350934617173779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5919020217076635916520309 554908145350934617173779)
    ·
      refine ⟨832362218026401925760669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554908145350934617173779 832362218026401925760669)
      ·
        refine ⟨312135831759900722160251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 832362218026401925760669 312135831759900722160251)
        ·
          refine ⟨468203747639851083240377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312135831759900722160251 468203747639851083240377)
          ·
            refine ⟨351152810729888312430283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468203747639851083240377 351152810729888312430283)
            ·
              refine ⟨526729216094832468645425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351152810729888312430283 526729216094832468645425)
              ·
                refine ⟨395046912071124351484069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 526729216094832468645425 395046912071124351484069)
                ·
                  refine ⟨74071296013335815903263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395046912071124351484069 74071296013335815903263)
                  ·
                    rfl

theorem cell20_162285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_162285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162285 prefixEnd_162285 := by exact prefixLift 162285
  have htrace : WordTrace (prefixWord ++ tailWord_162285) baseStart_162285 baseEnd_162285 := by
    simpa [prefixWord, tailWord_162285, baseEnd_162285] using wordTrace_append hprefix tailTrace_162285
  have hstable : (prefixWord ++ tailWord_162285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162285).length < 2 ^ (prefixWord ++ tailWord_162285).sum := by decide
  have hdescent : baseEnd_162285 < baseStart_162285 := by decide
  rcases family_descends (prefixWord ++ tailWord_162285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162316 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_162316 : Nat := 118140960795 + 162316 * 2 ^ 59
def prefixEnd_162316 : Nat := 4983230072969 + 3 ^ 40 * 162316 * 2
def baseEnd_162316 : Nat := 74085445258037485869803

theorem tailTrace_162316 : CollatzResearch.WordTrace tailWord_162316 prefixEnd_162316 74085445258037485869803 := by
  unfold tailWord_162316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960075439982164105449401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3946767253309552140599201 2960075439982164105449401)
  ·
    refine ⟨2220056579986623079087051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2960075439982164105449401 2220056579986623079087051)
    ·
      refine ⟨3330084869979934618630577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220056579986623079087051 3330084869979934618630577)
      ·
        refine ⟨2497563652484950963972933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330084869979934618630577 2497563652484950963972933)
        ·
          refine ⟨468293184840928305744925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2497563652484950963972933 468293184840928305744925)
          ·
            refine ⟨175609944315348114654347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 468293184840928305744925 175609944315348114654347)
            ·
              refine ⟨263414916473022171981521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175609944315348114654347 263414916473022171981521)
              ·
                refine ⟨197561187354766628986141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 263414916473022171981521 197561187354766628986141)
                ·
                  refine ⟨74085445258037485869803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197561187354766628986141 74085445258037485869803)
                  ·
                    rfl

theorem cell20_162316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_162316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162316 prefixEnd_162316 := by exact prefixLift 162316
  have htrace : WordTrace (prefixWord ++ tailWord_162316) baseStart_162316 baseEnd_162316 := by
    simpa [prefixWord, tailWord_162316, baseEnd_162316] using wordTrace_append hprefix tailTrace_162316
  have hstable : (prefixWord ++ tailWord_162316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162316).length < 2 ^ (prefixWord ++ tailWord_162316).sum := by decide
  have hdescent : baseEnd_162316 < baseStart_162316 := by decide
  rcases family_descends (prefixWord ++ tailWord_162316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162343 : List Nat := [1, 1, 7, 2, 2, 1, 2, 4]
def baseStart_162343 : Nat := 118140960795 + 162343 * 2 ^ 59
def prefixEnd_162343 : Nat := 4983230072969 + 3 ^ 40 * 162343 * 2
def baseEnd_162343 : Nat := 24699256264581797323231

theorem tailTrace_162343 : CollatzResearch.WordTrace tailWord_162343 prefixEnd_162343 24699256264581797323231 := by
  unfold tailWord_162343
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921135650866511822131683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3947423767244341214754455 5921135650866511822131683)
  ·
    refine ⟨8881703476299767733197525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5921135650866511822131683 8881703476299767733197525)
    ·
      refine ⟨208164925225775806246817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8881703476299767733197525 208164925225775806246817)
      ·
        refine ⟨156123693919331854685113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208164925225775806246817 156123693919331854685113)
        ·
          refine ⟨117092770439498891013835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156123693919331854685113 117092770439498891013835)
          ·
            refine ⟨175639155659248336520753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117092770439498891013835 175639155659248336520753)
            ·
              refine ⟨131729366744436252390565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175639155659248336520753 131729366744436252390565)
              ·
                refine ⟨24699256264581797323231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131729366744436252390565 24699256264581797323231)
                ·
                  rfl

theorem cell20_162343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_162343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162343 prefixEnd_162343 := by exact prefixLift 162343
  have htrace : WordTrace (prefixWord ++ tailWord_162343) baseStart_162343 baseEnd_162343 := by
    simpa [prefixWord, tailWord_162343, baseEnd_162343] using wordTrace_append hprefix tailTrace_162343
  have hstable : (prefixWord ++ tailWord_162343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162343).length < 2 ^ (prefixWord ++ tailWord_162343).sum := by decide
  have hdescent : baseEnd_162343 < baseStart_162343 := by decide
  rcases family_descends (prefixWord ++ tailWord_162343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162374 : List Nat := [6, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_162374 : Nat := 118140960795 + 162374 * 2 ^ 59
def prefixEnd_162374 : Nat := 4983230072969 + 3 ^ 40 * 162374 * 2
def baseEnd_162374 : Nat := 74111918038447061936233

theorem tailTrace_162374 : CollatzResearch.WordTrace tailWord_162374 prefixEnd_162374 74111918038447061936233 := by
  unfold tailWord_162374
  simp only [CollatzResearch.WordTrace]
  refine ⟨185070822304818878640943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3948177542502802744340117 185070822304818878640943)
  ·
    refine ⟨277606233457228317961415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185070822304818878640943 277606233457228317961415)
    ·
      refine ⟨416409350185842476942123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277606233457228317961415 416409350185842476942123)
      ·
        refine ⟨624614025278763715413185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416409350185842476942123 624614025278763715413185)
        ·
          refine ⟨468460518959072786559889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 624614025278763715413185 468460518959072786559889)
          ·
            refine ⟨351345389219304589919917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468460518959072786559889 351345389219304589919917)
            ·
              refine ⟨131754520957239221219969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351345389219304589919917 131754520957239221219969)
              ·
                refine ⟨98815890717929415914977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131754520957239221219969 98815890717929415914977)
                ·
                  refine ⟨74111918038447061936233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98815890717929415914977 74111918038447061936233)
                  ·
                    rfl

theorem cell20_162374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_162374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162374 prefixEnd_162374 := by exact prefixLift 162374
  have htrace : WordTrace (prefixWord ++ tailWord_162374) baseStart_162374 baseEnd_162374 := by
    simpa [prefixWord, tailWord_162374, baseEnd_162374] using wordTrace_append hprefix tailTrace_162374
  have hstable : (prefixWord ++ tailWord_162374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162374).length < 2 ^ (prefixWord ++ tailWord_162374).sum := by decide
  have hdescent : baseEnd_162374 < baseStart_162374 := by decide
  rcases family_descends (prefixWord ++ tailWord_162374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162378 : List Nat := [3, 1, 2, 1, 1, 5, 3, 2, 2]
def baseStart_162378 : Nat := 118140960795 + 162378 * 2 ^ 59
def prefixEnd_162378 : Nat := 4983230072969 + 3 ^ 40 * 162378 * 2
def baseEnd_162378 : Nat := 74113743747440825802883

theorem tailTrace_162378 : CollatzResearch.WordTrace tailWord_162378 prefixEnd_162378 74113743747440825802883 := by
  unfold tailWord_162378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480603051434928199913947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3948274803826475199770525 1480603051434928199913947)
  ·
    refine ⟨2220904577152392299870921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480603051434928199913947 2220904577152392299870921)
    ·
      refine ⟨1665678432864294224903191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2220904577152392299870921 1665678432864294224903191)
      ·
        refine ⟨2498517649296441337354787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665678432864294224903191 2498517649296441337354787)
        ·
          refine ⟨3747776473944662006032181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498517649296441337354787 3747776473944662006032181)
          ·
            refine ⟨351354044432312063065517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3747776473944662006032181 351354044432312063065517)
            ·
              refine ⟨131757766662117023649569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351354044432312063065517 131757766662117023649569)
              ·
                refine ⟨98818324996587767737177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131757766662117023649569 98818324996587767737177)
                ·
                  refine ⟨74113743747440825802883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98818324996587767737177 74113743747440825802883)
                  ·
                    rfl

theorem cell20_162378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_162378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162378 prefixEnd_162378 := by exact prefixLift 162378
  have htrace : WordTrace (prefixWord ++ tailWord_162378) baseStart_162378 baseEnd_162378 := by
    simpa [prefixWord, tailWord_162378, baseEnd_162378] using wordTrace_append hprefix tailTrace_162378
  have hstable : (prefixWord ++ tailWord_162378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162378).length < 2 ^ (prefixWord ++ tailWord_162378).sum := by decide
  have hdescent : baseEnd_162378 < baseStart_162378 := by decide
  rcases family_descends (prefixWord ++ tailWord_162378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162382 : List Nat := [4, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_162382 : Nat := 118140960795 + 162382 * 2 ^ 59
def prefixEnd_162382 : Nat := 4983230072969 + 3 ^ 40 * 162382 * 2
def baseEnd_162382 : Nat := 74115569456434589669533

theorem tailTrace_162382 : CollatzResearch.WordTrace tailWord_162382 prefixEnd_162382 74115569456434589669533 := by
  unfold tailWord_162382
  simp only [CollatzResearch.WordTrace]
  refine ⟨740319762215652685350175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3948372065150147655200933 740319762215652685350175)
  ·
    refine ⟨1110479643323479028025263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 740319762215652685350175 1110479643323479028025263)
    ·
      refine ⟨1665719464985218542037895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110479643323479028025263 1665719464985218542037895)
      ·
        refine ⟨2498579197477827813056843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665719464985218542037895 2498579197477827813056843)
        ·
          refine ⟨3747868796216741719585265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498579197477827813056843 3747868796216741719585265)
          ·
            refine ⟨2810901597162556289688949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3747868796216741719585265 2810901597162556289688949)
            ·
              refine ⟨263522024733989652158339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2810901597162556289688949 263522024733989652158339)
              ·
                refine ⟨395283037100984478237509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263522024733989652158339 395283037100984478237509)
                ·
                  refine ⟨74115569456434589669533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395283037100984478237509 74115569456434589669533)
                  ·
                    rfl

theorem cell20_162382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_162382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162382 prefixEnd_162382 := by exact prefixLift 162382
  have htrace : WordTrace (prefixWord ++ tailWord_162382) baseStart_162382 baseEnd_162382 := by
    simpa [prefixWord, tailWord_162382, baseEnd_162382] using wordTrace_append hprefix tailTrace_162382
  have hstable : (prefixWord ++ tailWord_162382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162382).length < 2 ^ (prefixWord ++ tailWord_162382).sum := by decide
  have hdescent : baseEnd_162382 < baseStart_162382 := by decide
  rcases family_descends (prefixWord ++ tailWord_162382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162403 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_162403 : Nat := 118140960795 + 162403 * 2 ^ 59
def prefixEnd_162403 : Nat := 4983230072969 + 3 ^ 40 * 162403 * 2
def baseEnd_162403 : Nat := 74125154428651849969447

theorem tailTrace_162403 : CollatzResearch.WordTrace tailWord_162403 prefixEnd_162403 74125154428651849969447 := by
  unfold tailWord_162403
  simp only [CollatzResearch.WordTrace]
  refine ⟨5923324030649142069315863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3948882687099428046210575 5923324030649142069315863)
  ·
    refine ⟨8884986045973713103973795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5923324030649142069315863 8884986045973713103973795)
    ·
      refine ⟨13327479068960569655960693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8884986045973713103973795 13327479068960569655960693)
      ·
        refine ⟨1249451162715053405246315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13327479068960569655960693 1249451162715053405246315)
        ·
          refine ⟨1874176744072580107869473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249451162715053405246315 1874176744072580107869473)
          ·
            refine ⟨1405632558054435080902105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1874176744072580107869473 1405632558054435080902105)
            ·
              refine ⟨1054224418540826310676579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1405632558054435080902105 1054224418540826310676579)
              ·
                refine ⟨1581336627811239466014869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054224418540826310676579 1581336627811239466014869)
                ·
                  refine ⟨74125154428651849969447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1581336627811239466014869 74125154428651849969447)
                  ·
                    rfl

theorem cell20_162403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_162403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162403 prefixEnd_162403 := by exact prefixLift 162403
  have htrace : WordTrace (prefixWord ++ tailWord_162403) baseStart_162403 baseEnd_162403 := by
    simpa [prefixWord, tailWord_162403, baseEnd_162403] using wordTrace_append hprefix tailTrace_162403
  have hstable : (prefixWord ++ tailWord_162403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162403).length < 2 ^ (prefixWord ++ tailWord_162403).sum := by decide
  have hdescent : baseEnd_162403 < baseStart_162403 := by decide
  rcases family_descends (prefixWord ++ tailWord_162403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162437 : List Nat := [1, 3, 1, 1, 4, 3, 1, 4, 2]
def baseStart_162437 : Nat := 118140960795 + 162437 * 2 ^ 59
def prefixEnd_162437 : Nat := 4983230072969 + 3 ^ 40 * 162437 * 2
def baseEnd_162437 : Nat := 74140672955098842835975

theorem tailTrace_162437 : CollatzResearch.WordTrace tailWord_162437 prefixEnd_162437 74140672955098842835975 := by
  unfold tailWord_162437
  simp only [CollatzResearch.WordTrace]
  refine ⟨5924564112525965876053565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3949709408350643917369043 5924564112525965876053565)
  ·
    refine ⟨2221711542197237203520087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5924564112525965876053565 2221711542197237203520087)
    ·
      refine ⟨3332567313295855805280131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2221711542197237203520087 3332567313295855805280131)
      ·
        refine ⟨4998850969943783707920197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3332567313295855805280131 4998850969943783707920197)
        ·
          refine ⟨937284556864459445235037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4998850969943783707920197 937284556864459445235037)
          ·
            refine ⟨351481708824172291963139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 937284556864459445235037 351481708824172291963139)
            ·
              refine ⟨527222563236258437944709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351481708824172291963139 527222563236258437944709)
              ·
                refine ⟨98854230606798457114633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527222563236258437944709 98854230606798457114633)
                ·
                  refine ⟨74140672955098842835975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98854230606798457114633 74140672955098842835975)
                  ·
                    rfl

theorem cell20_162437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 2].length) (baseStart_162437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162437 prefixEnd_162437 := by exact prefixLift 162437
  have htrace : WordTrace (prefixWord ++ tailWord_162437) baseStart_162437 baseEnd_162437 := by
    simpa [prefixWord, tailWord_162437, baseEnd_162437] using wordTrace_append hprefix tailTrace_162437
  have hstable : (prefixWord ++ tailWord_162437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162437).length < 2 ^ (prefixWord ++ tailWord_162437).sum := by decide
  have hdescent : baseEnd_162437 < baseStart_162437 := by decide
  rcases family_descends (prefixWord ++ tailWord_162437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162441 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 4]
def baseStart_162441 : Nat := 118140960795 + 162441 * 2 ^ 59
def prefixEnd_162441 : Nat := 4983230072969 + 3 ^ 40 * 162441 * 2
def baseEnd_162441 : Nat := 74142498664092606702625

theorem tailTrace_162441 : CollatzResearch.WordTrace tailWord_162441 prefixEnd_162441 74142498664092606702625 := by
  unfold tailWord_162441
  simp only [CollatzResearch.WordTrace]
  refine ⟨5924710004511474559199177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3949806669674316372799451 5924710004511474559199177)
  ·
    refine ⟨4443532503383605919399383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5924710004511474559199177 4443532503383605919399383)
    ·
      refine ⟨6665298755075408879099075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4443532503383605919399383 6665298755075408879099075)
      ·
        refine ⟨9997948132613113318648613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665298755075408879099075 9997948132613113318648613)
        ·
          refine ⟨1874615274864958747246615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9997948132613113318648613 1874615274864958747246615)
          ·
            refine ⟨2811922912297438120869923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874615274864958747246615 2811922912297438120869923)
            ·
              refine ⟨4217884368446157181304885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811922912297438120869923 4217884368446157181304885)
              ·
                refine ⟨395426659541827235747333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4217884368446157181304885 395426659541827235747333)
                ·
                  refine ⟨74142498664092606702625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395426659541827235747333 74142498664092606702625)
                  ·
                    rfl

theorem cell20_162441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_162441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162441 prefixEnd_162441 := by exact prefixLift 162441
  have htrace : WordTrace (prefixWord ++ tailWord_162441) baseStart_162441 baseEnd_162441 := by
    simpa [prefixWord, tailWord_162441, baseEnd_162441] using wordTrace_append hprefix tailTrace_162441
  have hstable : (prefixWord ++ tailWord_162441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162441).length < 2 ^ (prefixWord ++ tailWord_162441).sum := by decide
  have hdescent : baseEnd_162441 < baseStart_162441 := by decide
  rcases family_descends (prefixWord ++ tailWord_162441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162471 : List Nat := [1, 1, 6, 3, 1, 1, 2, 3, 2]
def baseStart_162471 : Nat := 118140960795 + 162471 * 2 ^ 59
def prefixEnd_162471 : Nat := 4983230072969 + 3 ^ 40 * 162471 * 2
def baseEnd_162471 : Nat := 74156191481545835702503

theorem tailTrace_162471 : CollatzResearch.WordTrace tailWord_162471 prefixEnd_162471 74156191481545835702503 := by
  unfold tailWord_162471
  simp only [CollatzResearch.WordTrace]
  refine ⟨5925804194402789682791267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3950536129601859788527511 5925804194402789682791267)
  ·
    refine ⟨8888706291604184524186901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5925804194402789682791267 8888706291604184524186901)
    ·
      refine ⟨416658107418946149571261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8888706291604184524186901 416658107418946149571261)
      ·
        refine ⟨156246790282104806089223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416658107418946149571261 156246790282104806089223)
        ·
          refine ⟨234370185423157209133835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156246790282104806089223 234370185423157209133835)
          ·
            refine ⟨351555278134735813700753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234370185423157209133835 351555278134735813700753)
            ·
              refine ⟨263666458601051860275565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351555278134735813700753 263666458601051860275565)
              ·
                refine ⟨98874921975394447603337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263666458601051860275565 98874921975394447603337)
                ·
                  refine ⟨74156191481545835702503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98874921975394447603337 74156191481545835702503)
                  ·
                    rfl

theorem cell20_162471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 3, 2].length) (baseStart_162471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162471 prefixEnd_162471 := by exact prefixLift 162471
  have htrace : WordTrace (prefixWord ++ tailWord_162471) baseStart_162471 baseEnd_162471 := by
    simpa [prefixWord, tailWord_162471, baseEnd_162471] using wordTrace_append hprefix tailTrace_162471
  have hstable : (prefixWord ++ tailWord_162471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162471).length < 2 ^ (prefixWord ++ tailWord_162471).sum := by decide
  have hdescent : baseEnd_162471 < baseStart_162471 := by decide
  rcases family_descends (prefixWord ++ tailWord_162471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162496 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_162496 : Nat := 118140960795 + 162496 * 2 ^ 59
def prefixEnd_162496 : Nat := 4983230072969 + 3 ^ 40 * 162496 * 2
def baseEnd_162496 : Nat := 74167602162756859869067

theorem tailTrace_162496 : CollatzResearch.WordTrace tailWord_162496 prefixEnd_162496 74167602162756859869067 := by
  unfold tailWord_162496
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963358009656109476225671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3951144012874812634967561 2963358009656109476225671)
  ·
    refine ⟨4445037014484164214338507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2963358009656109476225671 4445037014484164214338507)
    ·
      refine ⟨6667555521726246321507761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4445037014484164214338507 6667555521726246321507761)
      ·
        refine ⟨5000666641294684741130821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6667555521726246321507761 5000666641294684741130821)
        ·
          refine ⟨937624995242753388962029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5000666641294684741130821 937624995242753388962029)
          ·
            refine ⟨351609373216032520860761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 937624995242753388962029 351609373216032520860761)
            ·
              refine ⟨263707029912024390645571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351609373216032520860761 263707029912024390645571)
              ·
                refine ⟨395560544868036585968357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263707029912024390645571 395560544868036585968357)
                ·
                  refine ⟨74167602162756859869067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 395560544868036585968357 74167602162756859869067)
                  ·
                    rfl

theorem cell20_162496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_162496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162496 prefixEnd_162496 := by exact prefixLift 162496
  have htrace : WordTrace (prefixWord ++ tailWord_162496) baseStart_162496 baseEnd_162496 := by
    simpa [prefixWord, tailWord_162496, baseEnd_162496] using wordTrace_append hprefix tailTrace_162496
  have hstable : (prefixWord ++ tailWord_162496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162496).length < 2 ^ (prefixWord ++ tailWord_162496).sum := by decide
  have hdescent : baseEnd_162496 < baseStart_162496 := by decide
  rcases family_descends (prefixWord ++ tailWord_162496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162506 : List Nat := [3, 1, 2, 1, 4, 2, 3, 1, 3]
def baseStart_162506 : Nat := 118140960795 + 162506 * 2 ^ 59
def prefixEnd_162506 : Nat := 4983230072969 + 3 ^ 40 * 162506 * 2
def baseEnd_162506 : Nat := 74172166435241269535693

theorem tailTrace_162506 : CollatzResearch.WordTrace tailWord_162506 prefixEnd_162506 74172166435241269535693 := by
  unfold tailWord_162506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1481770187318997665078843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3951387166183993773543581 1481770187318997665078843)
  ·
    refine ⟨2222655280978496497618265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1481770187318997665078843 2222655280978496497618265)
    ·
      refine ⟨1666991460733872373213699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2222655280978496497618265 1666991460733872373213699)
      ·
        refine ⟨2500487191100808559820549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666991460733872373213699 2500487191100808559820549)
        ·
          refine ⟨468841348331401604966353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2500487191100808559820549 468841348331401604966353)
          ·
            refine ⟨351631011248551203724765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468841348331401604966353 351631011248551203724765)
            ·
              refine ⟨131861629218206701396787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351631011248551203724765 131861629218206701396787)
              ·
                refine ⟨197792443827310052095181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131861629218206701396787 197792443827310052095181)
                ·
                  refine ⟨74172166435241269535693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 197792443827310052095181 74172166435241269535693)
                  ·
                    rfl

theorem cell20_162506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_162506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162506 prefixEnd_162506 := by exact prefixLift 162506
  have htrace : WordTrace (prefixWord ++ tailWord_162506) baseStart_162506 baseEnd_162506 := by
    simpa [prefixWord, tailWord_162506, baseEnd_162506] using wordTrace_append hprefix tailTrace_162506
  have hstable : (prefixWord ++ tailWord_162506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162506).length < 2 ^ (prefixWord ++ tailWord_162506).sum := by decide
  have hdescent : baseEnd_162506 < baseStart_162506 := by decide
  rcases family_descends (prefixWord ++ tailWord_162506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162516 : List Nat := [2, 4, 1, 3, 3, 1, 2, 4]
def baseStart_162516 : Nat := 118140960795 + 162516 * 2 ^ 59
def prefixEnd_162516 : Nat := 4983230072969 + 3 ^ 40 * 162516 * 2
def baseEnd_162516 : Nat := 24725576902575226400773

theorem tailTrace_162516 : CollatzResearch.WordTrace tailWord_162516 prefixEnd_162516 24725576902575226400773 := by
  unfold tailWord_162516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963722739619881184089701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3951630319493174912119601 2963722739619881184089701)
  ·
    refine ⟨555698013678727722016819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2963722739619881184089701 555698013678727722016819)
    ·
      refine ⟨833547020518091583025229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555698013678727722016819 833547020518091583025229)
      ·
        refine ⟨312580132694284343634461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 833547020518091583025229 312580132694284343634461)
        ·
          refine ⟨117217549760356628862923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 312580132694284343634461 117217549760356628862923)
          ·
            refine ⟨175826324640534943294385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117217549760356628862923 175826324640534943294385)
            ·
              refine ⟨131869743480401207470789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175826324640534943294385 131869743480401207470789)
              ·
                refine ⟨24725576902575226400773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131869743480401207470789 24725576902575226400773)
                ·
                  rfl

theorem cell20_162516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_162516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162516 prefixEnd_162516 := by exact prefixLift 162516
  have htrace : WordTrace (prefixWord ++ tailWord_162516) baseStart_162516 baseEnd_162516 := by
    simpa [prefixWord, tailWord_162516, baseEnd_162516] using wordTrace_append hprefix tailTrace_162516
  have hstable : (prefixWord ++ tailWord_162516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162516).length < 2 ^ (prefixWord ++ tailWord_162516).sum := by decide
  have hdescent : baseEnd_162516 < baseStart_162516 := by decide
  rcases family_descends (prefixWord ++ tailWord_162516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162520 : List Nat := [2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_162520 : Nat := 118140960795 + 162520 * 2 ^ 59
def prefixEnd_162520 : Nat := 4983230072969 + 3 ^ 40 * 162520 * 2
def baseEnd_162520 : Nat := 24726185472239814356323

theorem tailTrace_162520 : CollatzResearch.WordTrace tailWord_162520 prefixEnd_162520 24726185472239814356323 := by
  unfold tailWord_162520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2963795685612635525662507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3951727580816847367550009 2963795685612635525662507)
  ·
    refine ⟨4445693528418953288493761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2963795685612635525662507 4445693528418953288493761)
    ·
      refine ⟨3334270146314214966370321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4445693528418953288493761 3334270146314214966370321)
      ·
        refine ⟨2500702609735661224777741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3334270146314214966370321 2500702609735661224777741)
        ·
          refine ⟨937763478650872959291653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2500702609735661224777741 937763478650872959291653)
          ·
            refine ⟨175830652247038679867185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 937763478650872959291653 175830652247038679867185)
            ·
              refine ⟨131872989185279009900389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175830652247038679867185 131872989185279009900389)
              ·
                refine ⟨24726185472239814356323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131872989185279009900389 24726185472239814356323)
                ·
                  rfl

theorem cell20_162520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_162520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162520 prefixEnd_162520 := by exact prefixLift 162520
  have htrace : WordTrace (prefixWord ++ tailWord_162520) baseStart_162520 baseEnd_162520 := by
    simpa [prefixWord, tailWord_162520, baseEnd_162520] using wordTrace_append hprefix tailTrace_162520
  have hstable : (prefixWord ++ tailWord_162520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162520).length < 2 ^ (prefixWord ++ tailWord_162520).sum := by decide
  have hdescent : baseEnd_162520 < baseStart_162520 := by decide
  rcases family_descends (prefixWord ++ tailWord_162520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162558 : List Nat := [4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_162558 : Nat := 118140960795 + 162558 * 2 ^ 59
def prefixEnd_162558 : Nat := 4983230072969 + 3 ^ 40 * 162558 * 2
def baseEnd_162558 : Nat := 24731966884053399934049

theorem tailTrace_162558 : CollatzResearch.WordTrace tailWord_162558 prefixEnd_162558 24731966884053399934049 := by
  unfold tailWord_162558
  simp only [CollatzResearch.WordTrace]
  refine ⟨741122168135950442651041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3952651563391735694138885 741122168135950442651041)
  ·
    refine ⟨555841626101962831988281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 741122168135950442651041 555841626101962831988281)
    ·
      refine ⟨416881219576472123991211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 555841626101962831988281 416881219576472123991211)
      ·
        refine ⟨625321829364708185986817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 416881219576472123991211 625321829364708185986817)
        ·
          refine ⟨468991372023531139490113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 625321829364708185986817 468991372023531139490113)
          ·
            refine ⟨351743529017648354617585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 468991372023531139490113 351743529017648354617585)
            ·
              refine ⟨263807646763236265963189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351743529017648354617585 263807646763236265963189)
              ·
                refine ⟨24731966884053399934049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 263807646763236265963189 24731966884053399934049)
                ·
                  rfl

theorem cell20_162558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_162558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162558 prefixEnd_162558 := by exact prefixLift 162558
  have htrace : WordTrace (prefixWord ++ tailWord_162558) baseStart_162558 baseEnd_162558 := by
    simpa [prefixWord, tailWord_162558, baseEnd_162558] using wordTrace_append hprefix tailTrace_162558
  have hstable : (prefixWord ++ tailWord_162558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162558).length < 2 ^ (prefixWord ++ tailWord_162558).sum := by decide
  have hdescent : baseEnd_162558 < baseStart_162558 := by decide
  rcases family_descends (prefixWord ++ tailWord_162558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162602 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 2]
def baseStart_162602 : Nat := 118140960795 + 162602 * 2 ^ 59
def prefixEnd_162602 : Nat := 4983230072969 + 3 ^ 40 * 162602 * 2
def baseEnd_162602 : Nat := 74215983451091602335301

theorem tailTrace_162602 : CollatzResearch.WordTrace tailWord_162602 prefixEnd_162602 74215983451091602335301 := by
  unfold tailWord_162602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1482645539232049763952515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3953721437952132703873373 1482645539232049763952515)
  ·
    refine ⟨2223968308848074645928773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1482645539232049763952515 2223968308848074645928773)
    ·
      refine ⟨416994057909013996111645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2223968308848074645928773 416994057909013996111645)
      ·
        refine ⟨156372771715880248541867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416994057909013996111645 156372771715880248541867)
        ·
          refine ⟨234559157573820372812801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156372771715880248541867 234559157573820372812801)
          ·
            refine ⟨175919368180365279609601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234559157573820372812801 175919368180365279609601)
            ·
              refine ⟨131939526135273959707201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 175919368180365279609601 131939526135273959707201)
              ·
                refine ⟨98954644601455469780401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131939526135273959707201 98954644601455469780401)
                ·
                  refine ⟨74215983451091602335301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98954644601455469780401 74215983451091602335301)
                  ·
                    rfl

theorem cell20_162602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 2].length) (baseStart_162602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162602 prefixEnd_162602 := by exact prefixLift 162602
  have htrace : WordTrace (prefixWord ++ tailWord_162602) baseStart_162602 baseEnd_162602 := by
    simpa [prefixWord, tailWord_162602, baseEnd_162602] using wordTrace_append hprefix tailTrace_162602
  have hstable : (prefixWord ++ tailWord_162602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162602).length < 2 ^ (prefixWord ++ tailWord_162602).sum := by decide
  have hdescent : baseEnd_162602 < baseStart_162602 := by decide
  rcases family_descends (prefixWord ++ tailWord_162602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162606 : List Nat := [4, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_162606 : Nat := 118140960795 + 162606 * 2 ^ 59
def prefixEnd_162606 : Nat := 4983230072969 + 3 ^ 40 * 162606 * 2
def baseEnd_162606 : Nat := 74217809160085366201951

theorem tailTrace_162606 : CollatzResearch.WordTrace tailWord_162606 prefixEnd_162606 74217809160085366201951 := by
  unfold tailWord_162606
  simp only [CollatzResearch.WordTrace]
  refine ⟨741341006114213467369459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3953818699275805159303781 741341006114213467369459)
  ·
    refine ⟨1112011509171320201054189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741341006114213467369459 1112011509171320201054189)
    ·
      refine ⟨417004315939245075395321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1112011509171320201054189 417004315939245075395321)
      ·
        refine ⟨312753236954433806546491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417004315939245075395321 312753236954433806546491)
        ·
          refine ⟨469129855431650709819737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 312753236954433806546491 469129855431650709819737)
          ·
            refine ⟨351847391573738032364803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 469129855431650709819737 351847391573738032364803)
            ·
              refine ⟨527771087360607048547205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351847391573738032364803 527771087360607048547205)
              ·
                refine ⟨98957078880113821602601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 527771087360607048547205 98957078880113821602601)
                ·
                  refine ⟨74217809160085366201951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98957078880113821602601 74217809160085366201951)
                  ·
                    rfl

theorem cell20_162606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_162606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162606 prefixEnd_162606 := by exact prefixLift 162606
  have htrace : WordTrace (prefixWord ++ tailWord_162606) baseStart_162606 baseEnd_162606 := by
    simpa [prefixWord, tailWord_162606, baseEnd_162606] using wordTrace_append hprefix tailTrace_162606
  have hstable : (prefixWord ++ tailWord_162606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162606).length < 2 ^ (prefixWord ++ tailWord_162606).sum := by decide
  have hdescent : baseEnd_162606 < baseStart_162606 := by decide
  rcases family_descends (prefixWord ++ tailWord_162606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162630 : List Nat := [6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_162630 : Nat := 118140960795 + 162630 * 2 ^ 59
def prefixEnd_162630 : Nat := 4983230072969 + 3 ^ 40 * 162630 * 2
def baseEnd_162630 : Nat := 24742921138015983133951

theorem tailTrace_162630 : CollatzResearch.WordTrace tailWord_162630 prefixEnd_162630 24742921138015983133951 := by
  unfold tailWord_162630
  simp only [CollatzResearch.WordTrace]
  refine ⟨185362606275836244932167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3954402267217839891886229 185362606275836244932167)
  ·
    refine ⟨278043909413754367398251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 185362606275836244932167 278043909413754367398251)
    ·
      refine ⟨417065864120631551097377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278043909413754367398251 417065864120631551097377)
      ·
        refine ⟨312799398090473663323033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 417065864120631551097377 312799398090473663323033)
        ·
          refine ⟨234599548567855247492275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312799398090473663323033 234599548567855247492275)
          ·
            refine ⟨351899322851782871238413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234599548567855247492275 351899322851782871238413)
            ·
              refine ⟨131962246069418576714405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351899322851782871238413 131962246069418576714405)
              ·
                refine ⟨24742921138015983133951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 131962246069418576714405 24742921138015983133951)
                ·
                  rfl

theorem cell20_162630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_162630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162630 prefixEnd_162630 := by exact prefixLift 162630
  have htrace : WordTrace (prefixWord ++ tailWord_162630) baseStart_162630 baseEnd_162630 := by
    simpa [prefixWord, tailWord_162630, baseEnd_162630] using wordTrace_append hprefix tailTrace_162630
  have hstable : (prefixWord ++ tailWord_162630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162630).length < 2 ^ (prefixWord ++ tailWord_162630).sum := by decide
  have hdescent : baseEnd_162630 < baseStart_162630 := by decide
  rcases family_descends (prefixWord ++ tailWord_162630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162638 : List Nat := [4, 1, 1, 1, 1, 1, 1, 10]
def baseStart_162638 : Nat := 118140960795 + 162638 * 2 ^ 59
def prefixEnd_162638 : Nat := 4983230072969 + 3 ^ 40 * 162638 * 2
def baseEnd_162638 : Nat := 24744138277345159045051

theorem tailTrace_162638 : CollatzResearch.WordTrace tailWord_162638 prefixEnd_162638 24744138277345159045051 := by
  unfold tailWord_162638
  simp only [CollatzResearch.WordTrace]
  refine ⟨741486898099722150515071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3954596789865184802747045 741486898099722150515071)
  ·
    refine ⟨1112230347149583225772607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 741486898099722150515071 1112230347149583225772607)
    ·
      refine ⟨1668345520724374838658911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112230347149583225772607 1668345520724374838658911)
      ·
        refine ⟨2502518281086562257988367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1668345520724374838658911 2502518281086562257988367)
        ·
          refine ⟨3753777421629843386982551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2502518281086562257988367 3753777421629843386982551)
          ·
            refine ⟨5630666132444765080473827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753777421629843386982551 5630666132444765080473827)
            ·
              refine ⟨8445999198667147620710741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5630666132444765080473827 8445999198667147620710741)
              ·
                refine ⟨24744138277345159045051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8445999198667147620710741 24744138277345159045051)
                ·
                  rfl

theorem cell20_162638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_162638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162638 prefixEnd_162638 := by exact prefixLift 162638
  have htrace : WordTrace (prefixWord ++ tailWord_162638) baseStart_162638 baseEnd_162638 := by
    simpa [prefixWord, tailWord_162638, baseEnd_162638] using wordTrace_append hprefix tailTrace_162638
  have hstable : (prefixWord ++ tailWord_162638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162638).length < 2 ^ (prefixWord ++ tailWord_162638).sum := by decide
  have hdescent : baseEnd_162638 < baseStart_162638 := by decide
  rcases family_descends (prefixWord ++ tailWord_162638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162644 : List Nat := [2, 4, 1, 1, 4, 1, 2, 3, 2]
def baseStart_162644 : Nat := 118140960795 + 162644 * 2 ^ 59
def prefixEnd_162644 : Nat := 4983230072969 + 3 ^ 40 * 162644 * 2
def baseEnd_162644 : Nat := 74235153395526122935129

theorem tailTrace_162644 : CollatzResearch.WordTrace tailWord_162644 prefixEnd_162644 74235153395526122935129 := by
  unfold tailWord_162644
  simp only [CollatzResearch.WordTrace]
  refine ⟨2966057011388020114419493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3954742681850693485892657 2966057011388020114419493)
  ·
    refine ⟨556135689635253771453655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2966057011388020114419493 556135689635253771453655)
    ·
      refine ⟨834203534452880657180483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 556135689635253771453655 834203534452880657180483)
      ·
        refine ⟨1251305301679320985770725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834203534452880657180483 1251305301679320985770725)
        ·
          refine ⟨234619744064872684832011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1251305301679320985770725 234619744064872684832011)
          ·
            refine ⟨351929616097309027248017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234619744064872684832011 351929616097309027248017)
            ·
              refine ⟨263947212072981770436013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351929616097309027248017 263947212072981770436013)
              ·
                refine ⟨98980204527368163913505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 263947212072981770436013 98980204527368163913505)
                ·
                  refine ⟨74235153395526122935129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 98980204527368163913505 74235153395526122935129)
                  ·
                    rfl

theorem cell20_162644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_162644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162644 prefixEnd_162644 := by exact prefixLift 162644
  have htrace : WordTrace (prefixWord ++ tailWord_162644) baseStart_162644 baseEnd_162644 := by
    simpa [prefixWord, tailWord_162644, baseEnd_162644] using wordTrace_append hprefix tailTrace_162644
  have hstable : (prefixWord ++ tailWord_162644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162644).length < 2 ^ (prefixWord ++ tailWord_162644).sum := by decide
  have hdescent : baseEnd_162644 < baseStart_162644 := by decide
  rcases family_descends (prefixWord ++ tailWord_162644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162693 : List Nat := [1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_162693 : Nat := 118140960795 + 162693 * 2 ^ 59
def prefixEnd_162693 : Nat := 4983230072969 + 3 ^ 40 * 162693 * 2
def baseEnd_162693 : Nat := 24752506110233243433865

theorem tailTrace_162693 : CollatzResearch.WordTrace tailWord_162693 prefixEnd_162693 24752506110233243433865 := by
  unfold tailWord_162693
  simp only [CollatzResearch.WordTrace]
  refine ⟨5933901199598521597372733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3955934133065681064915155 5933901199598521597372733)
  ·
    refine ⟨2225212949849445599014775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5933901199598521597372733 2225212949849445599014775)
    ·
      refine ⟨3337819424774168398522163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2225212949849445599014775 3337819424774168398522163)
      ·
        refine ⟨5006729137161252597783245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3337819424774168398522163 5006729137161252597783245)
        ·
          refine ⟨1877523426435469724168717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5006729137161252597783245 1877523426435469724168717)
          ·
            refine ⟨704071284913301146563269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1877523426435469724168717 704071284913301146563269)
            ·
              refine ⟨132013365921243964980613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 704071284913301146563269 132013365921243964980613)
              ·
                refine ⟨24752506110233243433865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132013365921243964980613 24752506110233243433865)
                ·
                  rfl

theorem cell20_162693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_162693 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162693 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162693 prefixEnd_162693 := by exact prefixLift 162693
  have htrace : WordTrace (prefixWord ++ tailWord_162693) baseStart_162693 baseEnd_162693 := by
    simpa [prefixWord, tailWord_162693, baseEnd_162693] using wordTrace_append hprefix tailTrace_162693
  have hstable : (prefixWord ++ tailWord_162693).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162693).length < 2 ^ (prefixWord ++ tailWord_162693).sum := by decide
  have hdescent : baseEnd_162693 < baseStart_162693 := by decide
  rcases family_descends (prefixWord ++ tailWord_162693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162752 : List Nat := [2, 1, 1, 2, 3, 3, 2, 6]
def baseStart_162752 : Nat := 118140960795 + 162752 * 2 ^ 59
def prefixEnd_162752 : Nat := 4983230072969 + 3 ^ 40 * 162752 * 2
def baseEnd_162752 : Nat := 24761482512785915778229

theorem tailTrace_162752 : CollatzResearch.WordTrace tailWord_162752 prefixEnd_162752 24761482512785915778229 := by
  unfold tailWord_162752
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968026553192387336885255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3957368737589849782513673 2968026553192387336885255)
  ·
    refine ⟨4452039829788581005327883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2968026553192387336885255 4452039829788581005327883)
    ·
      refine ⟨6678059744682871507991825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4452039829788581005327883 6678059744682871507991825)
      ·
        refine ⟨5008544808512153630993869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6678059744682871507991825 5008544808512153630993869)
        ·
          refine ⟨1878204303192057611622701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5008544808512153630993869 1878204303192057611622701)
          ·
            refine ⟨704326613697021604358513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1878204303192057611622701 704326613697021604358513)
            ·
              refine ⟨528244960272766203268885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 704326613697021604358513 528244960272766203268885)
              ·
                refine ⟨24761482512785915778229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 528244960272766203268885 24761482512785915778229)
                ·
                  rfl

theorem cell20_162752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_162752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162752 prefixEnd_162752 := by exact prefixLift 162752
  have htrace : WordTrace (prefixWord ++ tailWord_162752) baseStart_162752 baseEnd_162752 := by
    simpa [prefixWord, tailWord_162752, baseEnd_162752] using wordTrace_append hprefix tailTrace_162752
  have hstable : (prefixWord ++ tailWord_162752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162752).length < 2 ^ (prefixWord ++ tailWord_162752).sum := by decide
  have hdescent : baseEnd_162752 < baseStart_162752 := by decide
  rcases family_descends (prefixWord ++ tailWord_162752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162759 : List Nat := [1, 1, 4, 1, 1, 2, 2, 1, 7]
def baseStart_162759 : Nat := 118140960795 + 162759 * 2 ^ 59
def prefixEnd_162759 : Nat := 4983230072969 + 3 ^ 40 * 162759 * 2
def baseEnd_162759 : Nat := 74287642529096834101325

theorem tailTrace_162759 : CollatzResearch.WordTrace tailWord_162759 prefixEnd_162759 74287642529096834101325 := by
  unfold tailWord_162759
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936308417359414869275331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3957538944906276579516887 5936308417359414869275331)
  ·
    refine ⟨8904462626039122303912997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5936308417359414869275331 8904462626039122303912997)
    ·
      refine ⟨1669586742382335431983687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8904462626039122303912997 1669586742382335431983687)
      ·
        refine ⟨2504380113573503147975531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669586742382335431983687 2504380113573503147975531)
        ·
          refine ⟨3756570170360254721963297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504380113573503147975531 3756570170360254721963297)
          ·
            refine ⟨2817427627770191041472473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3756570170360254721963297 2817427627770191041472473)
            ·
              refine ⟨2113070720827643281104355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2817427627770191041472473 2113070720827643281104355)
              ·
                refine ⟨3169606081241464921656533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113070720827643281104355 3169606081241464921656533)
                ·
                  refine ⟨74287642529096834101325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3169606081241464921656533 74287642529096834101325)
                  ·
                    rfl

theorem cell20_162759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_162759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162759 prefixEnd_162759 := by exact prefixLift 162759
  have htrace : WordTrace (prefixWord ++ tailWord_162759) baseStart_162759 baseEnd_162759 := by
    simpa [prefixWord, tailWord_162759, baseEnd_162759] using wordTrace_append hprefix tailTrace_162759
  have hstable : (prefixWord ++ tailWord_162759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162759).length < 2 ^ (prefixWord ++ tailWord_162759).sum := by decide
  have hdescent : baseEnd_162759 < baseStart_162759 := by decide
  rcases family_descends (prefixWord ++ tailWord_162759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162762 : List Nat := [3, 1, 2, 1, 2, 1, 1, 7, 2]
def baseStart_162762 : Nat := 118140960795 + 162762 * 2 ^ 59
def prefixEnd_162762 : Nat := 4983230072969 + 3 ^ 40 * 162762 * 2
def baseEnd_162762 : Nat := 74289011810842157001313

theorem tailTrace_162762 : CollatzResearch.WordTrace tailWord_162762 prefixEnd_162762 74289011810842157001313 := by
  unfold tailWord_162762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484104459087136595408635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3957611890899030921089693 1484104459087136595408635)
  ·
    refine ⟨2226156688630704893112953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1484104459087136595408635 2226156688630704893112953)
    ·
      refine ⟨1669617516473028669834715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2226156688630704893112953 1669617516473028669834715)
      ·
        refine ⟨2504426274709543004752073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669617516473028669834715 2504426274709543004752073)
        ·
          refine ⟨1878319706032157253564055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504426274709543004752073 1878319706032157253564055)
          ·
            refine ⟨2817479559048235880346083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878319706032157253564055 2817479559048235880346083)
            ·
              refine ⟨4226219338572353820519125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817479559048235880346083 4226219338572353820519125)
              ·
                refine ⟨99052015747789542668417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4226219338572353820519125 99052015747789542668417)
                ·
                  refine ⟨74289011810842157001313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99052015747789542668417 74289011810842157001313)
                  ·
                    rfl

theorem cell20_162762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_162762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162762 prefixEnd_162762 := by exact prefixLift 162762
  have htrace : WordTrace (prefixWord ++ tailWord_162762) baseStart_162762 baseEnd_162762 := by
    simpa [prefixWord, tailWord_162762, baseEnd_162762] using wordTrace_append hprefix tailTrace_162762
  have hstable : (prefixWord ++ tailWord_162762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162762).length < 2 ^ (prefixWord ++ tailWord_162762).sum := by decide
  have hdescent : baseEnd_162762 < baseStart_162762 := by decide
  rcases family_descends (prefixWord ++ tailWord_162762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162765 : List Nat := [1, 6, 3, 1, 1, 8]
def baseStart_162765 : Nat := 118140960795 + 162765 * 2 ^ 59
def prefixEnd_162765 : Nat := 4983230072969 + 3 ^ 40 * 162765 * 2
def baseEnd_162765 : Nat := 2751495596021758514863

theorem tailTrace_162765 : CollatzResearch.WordTrace tailWord_162765 prefixEnd_162765 2751495596021758514863 := by
  unfold tailWord_162765
  simp only [CollatzResearch.WordTrace]
  refine ⟨5936527255337677893993749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3957684836891785262662499 5936527255337677893993749)
  ·
    refine ⟨278274715093953651280957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5936527255337677893993749 278274715093953651280957)
    ·
      refine ⟨104353018160232619230359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 278274715093953651280957 104353018160232619230359)
      ·
        refine ⟨156529527240348928845539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104353018160232619230359 156529527240348928845539)
        ·
          refine ⟨234794290860523393268309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156529527240348928845539 234794290860523393268309)
          ·
            refine ⟨2751495596021758514863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 234794290860523393268309 2751495596021758514863)
            ·
              rfl

theorem cell20_162765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 8].length) (baseStart_162765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162765 prefixEnd_162765 := by exact prefixLift 162765
  have htrace : WordTrace (prefixWord ++ tailWord_162765) baseStart_162765 baseEnd_162765 := by
    simpa [prefixWord, tailWord_162765, baseEnd_162765] using wordTrace_append hprefix tailTrace_162765
  have hstable : (prefixWord ++ tailWord_162765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162765).length < 2 ^ (prefixWord ++ tailWord_162765).sum := by decide
  have hdescent : baseEnd_162765 < baseStart_162765 := by decide
  rcases family_descends (prefixWord ++ tailWord_162765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162776 : List Nat := [2, 1, 2, 2, 2, 3, 1, 4, 3]
def baseStart_162776 : Nat := 118140960795 + 162776 * 2 ^ 59
def prefixEnd_162776 : Nat := 4983230072969 + 3 ^ 40 * 162776 * 2
def baseEnd_162776 : Nat := 74295401792320330534589

theorem tailTrace_162776 : CollatzResearch.WordTrace tailWord_162776 prefixEnd_162776 74295401792320330534589 := by
  unfold tailWord_162776
  simp only [CollatzResearch.WordTrace]
  refine ⟨2968464229148913386322091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3957952305531884515096121 2968464229148913386322091)
  ·
    refine ⟨4452696343723370079483137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2968464229148913386322091 4452696343723370079483137)
    ·
      refine ⟨3339522257792527559612353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4452696343723370079483137 3339522257792527559612353)
      ·
        refine ⟨2504641693344395669709265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339522257792527559612353 2504641693344395669709265)
        ·
          refine ⟨1878481270008296752281949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504641693344395669709265 1878481270008296752281949)
          ·
            refine ⟨704430476253111282105731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1878481270008296752281949 704430476253111282105731)
            ·
              refine ⟨1056645714379666923158597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 704430476253111282105731 1056645714379666923158597)
              ·
                refine ⟨198121071446187548092237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1056645714379666923158597 198121071446187548092237)
                ·
                  refine ⟨74295401792320330534589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198121071446187548092237 74295401792320330534589)
                  ·
                    rfl

theorem cell20_162776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 4, 3].length) (baseStart_162776 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162776 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162776 prefixEnd_162776 := by exact prefixLift 162776
  have htrace : WordTrace (prefixWord ++ tailWord_162776) baseStart_162776 baseEnd_162776 := by
    simpa [prefixWord, tailWord_162776, baseEnd_162776] using wordTrace_append hprefix tailTrace_162776
  have hstable : (prefixWord ++ tailWord_162776).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162776).length < 2 ^ (prefixWord ++ tailWord_162776).sum := by decide
  have hdescent : baseEnd_162776 < baseStart_162776 := by decide
  rcases family_descends (prefixWord ++ tailWord_162776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162786 : List Nat := [3, 3, 3, 1, 1, 1, 3, 5]
def baseStart_162786 : Nat := 118140960795 + 162786 * 2 ^ 59
def prefixEnd_162786 : Nat := 4983230072969 + 3 ^ 40 * 162786 * 2
def baseEnd_162786 : Nat := 24766655354934913400405

theorem tailTrace_162786 : CollatzResearch.WordTrace tailWord_162786 prefixEnd_162786 24766655354934913400405 := by
  unfold tailWord_162786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1484323297065399620127053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3958195458841065653672141 1484323297065399620127053)
  ·
    refine ⟨556621236399524857547645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1484323297065399620127053 556621236399524857547645)
    ·
      refine ⟨208732963649821821580367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 556621236399524857547645 208732963649821821580367)
      ·
        refine ⟨313099445474732732370551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208732963649821821580367 313099445474732732370551)
        ·
          refine ⟨469649168212099098555827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313099445474732732370551 469649168212099098555827)
          ·
            refine ⟨704473752318148647833741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 469649168212099098555827 704473752318148647833741)
            ·
              refine ⟨264177657119305742937653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 704473752318148647833741 264177657119305742937653)
              ·
                refine ⟨24766655354934913400405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264177657119305742937653 24766655354934913400405)
                ·
                  rfl

theorem cell20_162786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_162786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162786 prefixEnd_162786 := by exact prefixLift 162786
  have htrace : WordTrace (prefixWord ++ tailWord_162786) baseStart_162786 baseEnd_162786 := by
    simpa [prefixWord, tailWord_162786, baseEnd_162786] using wordTrace_append hprefix tailTrace_162786
  have hstable : (prefixWord ++ tailWord_162786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162786).length < 2 ^ (prefixWord ++ tailWord_162786).sum := by decide
  have hdescent : baseEnd_162786 < baseStart_162786 := by decide
  rcases family_descends (prefixWord ++ tailWord_162786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162817 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 2]
def baseStart_162817 : Nat := 118140960795 + 162817 * 2 ^ 59
def prefixEnd_162817 : Nat := 4983230072969 + 3 ^ 40 * 162817 * 2
def baseEnd_162817 : Nat := 74314115309506410167755

theorem tailTrace_162817 : CollatzResearch.WordTrace tailWord_162817 prefixEnd_162817 74314115309506410167755 := by
  unfold tailWord_162817
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938423851149290774886705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3958949234099527183257803 5938423851149290774886705)
  ·
    refine ⟨4453817888361968081165029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5938423851149290774886705 4453817888361968081165029)
    ·
      refine ⟨835090854067869015218443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4453817888361968081165029 835090854067869015218443)
      ·
        refine ⟨1252636281101803522827665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835090854067869015218443 1252636281101803522827665)
        ·
          refine ⟨939477210826352642120749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1252636281101803522827665 939477210826352642120749)
          ·
            refine ⟨352303954059882240795281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 939477210826352642120749 352303954059882240795281)
            ·
              refine ⟨264227965544911680596461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352303954059882240795281 264227965544911680596461)
              ·
                refine ⟨99085487079341880223673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264227965544911680596461 99085487079341880223673)
                ·
                  refine ⟨74314115309506410167755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99085487079341880223673 74314115309506410167755)
                  ·
                    rfl

theorem cell20_162817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_162817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162817 prefixEnd_162817 := by exact prefixLift 162817
  have htrace : WordTrace (prefixWord ++ tailWord_162817) baseStart_162817 baseEnd_162817 := by
    simpa [prefixWord, tailWord_162817, baseEnd_162817] using wordTrace_append hprefix tailTrace_162817
  have hstable : (prefixWord ++ tailWord_162817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162817).length < 2 ^ (prefixWord ++ tailWord_162817).sum := by decide
  have hdescent : baseEnd_162817 < baseStart_162817 := by decide
  rcases family_descends (prefixWord ++ tailWord_162817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162828 : List Nat := [2, 2, 1, 2, 3, 3, 7]
def baseStart_162828 : Nat := 118140960795 + 162828 * 2 ^ 59
def prefixEnd_162828 : Nat := 4983230072969 + 3 ^ 40 * 162828 * 2
def baseEnd_162828 : Nat := 8257681778804362311227

theorem tailTrace_162828 : CollatzResearch.WordTrace tailWord_162828 prefixEnd_162828 8257681778804362311227 := by
  unfold tailWord_162828
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969412527054719826768569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3959216702739626435691425 2969412527054719826768569)
  ·
    refine ⟨2227059395291039870076427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2969412527054719826768569 2227059395291039870076427)
    ·
      refine ⟨3340589092936559805114641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227059395291039870076427 3340589092936559805114641)
      ·
        refine ⟨2505441819702419853835981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3340589092936559805114641 2505441819702419853835981)
        ·
          refine ⟨939540682388407445188493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2505441819702419853835981 939540682388407445188493)
          ·
            refine ⟨352327755895652791945685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 939540682388407445188493 352327755895652791945685)
            ·
              refine ⟨8257681778804362311227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 352327755895652791945685 8257681778804362311227)
              ·
                rfl

theorem cell20_162828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_162828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162828 prefixEnd_162828 := by exact prefixLift 162828
  have htrace : WordTrace (prefixWord ++ tailWord_162828) baseStart_162828 baseEnd_162828 := by
    simpa [prefixWord, tailWord_162828, baseEnd_162828] using wordTrace_append hprefix tailTrace_162828
  have hstable : (prefixWord ++ tailWord_162828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162828).length < 2 ^ (prefixWord ++ tailWord_162828).sum := by decide
  have hdescent : baseEnd_162828 < baseStart_162828 := by decide
  rcases family_descends (prefixWord ++ tailWord_162828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162866 : List Nat := [3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_162866 : Nat := 118140960795 + 162866 * 2 ^ 59
def prefixEnd_162866 : Nat := 4983230072969 + 3 ^ 40 * 162866 * 2
def baseEnd_162866 : Nat := 24778826748226672511407

theorem tailTrace_162866 : CollatzResearch.WordTrace tailWord_162866 prefixEnd_162866 24778826748226672511407 := by
  unfold tailWord_162866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1485052756992943035855113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3960140685314514762280301 1485052756992943035855113)
  ·
    refine ⟨1113789567744707276891335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1485052756992943035855113 1113789567744707276891335)
    ·
      refine ⟨1670684351617060915337003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1113789567744707276891335 1670684351617060915337003)
      ·
        refine ⟨2506026527425591373005505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670684351617060915337003 2506026527425591373005505)
        ·
          refine ⟨1879519895569193529754129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2506026527425591373005505 1879519895569193529754129)
          ·
            refine ⟨1409639921676895147315597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1879519895569193529754129 1409639921676895147315597)
            ·
              refine ⟨528614970628835680243349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1409639921676895147315597 528614970628835680243349)
              ·
                refine ⟨24778826748226672511407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 528614970628835680243349 24778826748226672511407)
                ·
                  rfl

theorem cell20_162866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_162866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162866 prefixEnd_162866 := by exact prefixLift 162866
  have htrace : WordTrace (prefixWord ++ tailWord_162866) baseStart_162866 baseEnd_162866 := by
    simpa [prefixWord, tailWord_162866, baseEnd_162866] using wordTrace_append hprefix tailTrace_162866
  have hstable : (prefixWord ++ tailWord_162866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162866).length < 2 ^ (prefixWord ++ tailWord_162866).sum := by decide
  have hdescent : baseEnd_162866 < baseStart_162866 := by decide
  rcases family_descends (prefixWord ++ tailWord_162866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162893 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 4]
def baseStart_162893 : Nat := 118140960795 + 162893 * 2 ^ 59
def prefixEnd_162893 : Nat := 4983230072969 + 3 ^ 40 * 162893 * 2
def baseEnd_162893 : Nat := 74348803780387923634111

theorem tailTrace_162893 : CollatzResearch.WordTrace tailWord_162893 prefixEnd_162893 74348803780387923634111 := by
  unfold tailWord_162893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941195798873955754653333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3960797199249303836435555 5941195798873955754653333)
  ·
    refine ⟨278493553072216675999375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5941195798873955754653333 278493553072216675999375)
    ·
      refine ⟨417740329608325013999063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 278493553072216675999375 417740329608325013999063)
      ·
        refine ⟨626610494412487520998595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 417740329608325013999063 626610494412487520998595)
        ·
          refine ⟨939915741618731281497893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 626610494412487520998595 939915741618731281497893)
          ·
            refine ⟨176234201553512115280855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 939915741618731281497893 176234201553512115280855)
            ·
              refine ⟨264351302330268172921283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176234201553512115280855 264351302330268172921283)
              ·
                refine ⟨396526953495402259381925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264351302330268172921283 396526953495402259381925)
                ·
                  refine ⟨74348803780387923634111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396526953495402259381925 74348803780387923634111)
                  ·
                    rfl

theorem cell20_162893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_162893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162893 prefixEnd_162893 := by exact prefixLift 162893
  have htrace : WordTrace (prefixWord ++ tailWord_162893) baseStart_162893 baseEnd_162893 := by
    simpa [prefixWord, tailWord_162893, baseEnd_162893] using wordTrace_append hprefix tailTrace_162893
  have hstable : (prefixWord ++ tailWord_162893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162893).length < 2 ^ (prefixWord ++ tailWord_162893).sum := by decide
  have hdescent : baseEnd_162893 < baseStart_162893 := by decide
  rcases family_descends (prefixWord ++ tailWord_162893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162897 : List Nat := [1, 2, 2, 1, 3, 1, 5, 1, 4]
def baseStart_162897 : Nat := 118140960795 + 162897 * 2 ^ 59
def prefixEnd_162897 : Nat := 4983230072969 + 3 ^ 40 * 162897 * 2
def baseEnd_162897 : Nat := 74350629489381687500761

theorem tailTrace_162897 : CollatzResearch.WordTrace tailWord_162897 prefixEnd_162897 74350629489381687500761 := by
  unfold tailWord_162897
  simp only [CollatzResearch.WordTrace]
  refine ⟨5941341690859464437798945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3960894460572976291865963 5941341690859464437798945)
  ·
    refine ⟨4456006268144598328349209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5941341690859464437798945 4456006268144598328349209)
    ·
      refine ⟨3342004701108448746261907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4456006268144598328349209 3342004701108448746261907)
      ·
        refine ⟨5013007051662673119392861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342004701108448746261907 5013007051662673119392861)
        ·
          refine ⟨1879877644373502419772323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5013007051662673119392861 1879877644373502419772323)
          ·
            refine ⟨2819816466560253629658485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879877644373502419772323 2819816466560253629658485)
            ·
              refine ⟨264357793740023777780483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2819816466560253629658485 264357793740023777780483)
              ·
                refine ⟨396536690610035666670725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 264357793740023777780483 396536690610035666670725)
                ·
                  refine ⟨74350629489381687500761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396536690610035666670725 74350629489381687500761)
                  ·
                    rfl

theorem cell20_162897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_162897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162897 prefixEnd_162897 := by exact prefixLift 162897
  have htrace : WordTrace (prefixWord ++ tailWord_162897) baseStart_162897 baseEnd_162897 := by
    simpa [prefixWord, tailWord_162897, baseEnd_162897] using wordTrace_append hprefix tailTrace_162897
  have hstable : (prefixWord ++ tailWord_162897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162897).length < 2 ^ (prefixWord ++ tailWord_162897).sum := by decide
  have hdescent : baseEnd_162897 < baseStart_162897 := by decide
  rcases family_descends (prefixWord ++ tailWord_162897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162904 : List Nat := [2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_162904 : Nat := 118140960795 + 162904 * 2 ^ 59
def prefixEnd_162904 : Nat := 4983230072969 + 3 ^ 40 * 162904 * 2
def baseEnd_162904 : Nat := 24784608160040258089133

theorem tailTrace_162904 : CollatzResearch.WordTrace tailWord_162904 prefixEnd_162904 24784608160040258089133 := by
  unfold tailWord_162904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2970798500917052316651883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3961064667889403088869177 2970798500917052316651883)
  ·
    refine ⟨4456197751375578474977825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2970798500917052316651883 4456197751375578474977825)
    ·
      refine ⟨3342148313531683856233369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4456197751375578474977825 3342148313531683856233369)
      ·
        refine ⟨2506611235148762892175027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3342148313531683856233369 2506611235148762892175027)
        ·
          refine ⟨3759916852723144338262541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2506611235148762892175027 3759916852723144338262541)
          ·
            refine ⟨1409968819771179126848453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3759916852723144338262541 1409968819771179126848453)
            ·
              refine ⟨264369153707096086284085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1409968819771179126848453 264369153707096086284085)
              ·
                refine ⟨24784608160040258089133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264369153707096086284085 24784608160040258089133)
                ·
                  rfl

theorem cell20_162904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_162904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162904 prefixEnd_162904 := by exact prefixLift 162904
  have htrace : WordTrace (prefixWord ++ tailWord_162904) baseStart_162904 baseEnd_162904 := by
    simpa [prefixWord, tailWord_162904, baseEnd_162904] using wordTrace_append hprefix tailTrace_162904
  have hstable : (prefixWord ++ tailWord_162904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162904).length < 2 ^ (prefixWord ++ tailWord_162904).sum := by decide
  have hdescent : baseEnd_162904 < baseStart_162904 := by decide
  rcases family_descends (prefixWord ++ tailWord_162904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162945 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 3]
def baseStart_162945 : Nat := 118140960795 + 162945 * 2 ^ 59
def prefixEnd_162945 : Nat := 4983230072969 + 3 ^ 40 * 162945 * 2
def baseEnd_162945 : Nat := 74372537997306853900565

theorem tailTrace_162945 : CollatzResearch.WordTrace tailWord_162945 prefixEnd_162945 74372537997306853900565 := by
  unfold tailWord_162945
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943092394685568635546289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3962061596457045757030859 5943092394685568635546289)
  ·
    refine ⟨4457319296014176476659717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5943092394685568635546289 4457319296014176476659717)
    ·
      refine ⟨835747368002658089373697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4457319296014176476659717 835747368002658089373697)
      ·
        refine ⟨626810526001993567030273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 835747368002658089373697 626810526001993567030273)
        ·
          refine ⟨470107894501495175272705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 626810526001993567030273 470107894501495175272705)
          ·
            refine ⟨352580920876121381454529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470107894501495175272705 352580920876121381454529)
            ·
              refine ⟨264435690657091036090897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352580920876121381454529 264435690657091036090897)
              ·
                refine ⟨198326767992818277068173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264435690657091036090897 198326767992818277068173)
                ·
                  refine ⟨74372537997306853900565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198326767992818277068173 74372537997306853900565)
                  ·
                    rfl

theorem cell20_162945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_162945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162945 prefixEnd_162945 := by exact prefixLift 162945
  have htrace : WordTrace (prefixWord ++ tailWord_162945) baseStart_162945 baseEnd_162945 := by
    simpa [prefixWord, tailWord_162945, baseEnd_162945] using wordTrace_append hprefix tailTrace_162945
  have hstable : (prefixWord ++ tailWord_162945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162945).length < 2 ^ (prefixWord ++ tailWord_162945).sum := by decide
  have hdescent : baseEnd_162945 < baseStart_162945 := by decide
  rcases family_descends (prefixWord ++ tailWord_162945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162948 : List Nat := [2, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_162948 : Nat := 118140960795 + 162948 * 2 ^ 59
def prefixEnd_162948 : Nat := 4983230072969 + 3 ^ 40 * 162948 * 2
def baseEnd_162948 : Nat := 74373907279052176800553

theorem tailTrace_162948 : CollatzResearch.WordTrace tailWord_162948 prefixEnd_162948 74373907279052176800553 := by
  unfold tailWord_162948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971600906837350073952749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3962134542449800098603665 2971600906837350073952749)
  ·
    refine ⟨1114350340064006277732281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2971600906837350073952749 1114350340064006277732281)
    ·
      refine ⟨835762755048004708299211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1114350340064006277732281 835762755048004708299211)
      ·
        refine ⟨1253644132572007062448817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835762755048004708299211 1253644132572007062448817)
        ·
          refine ⟨940233099429005296836613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1253644132572007062448817 940233099429005296836613)
          ·
            refine ⟨176293706142938493156865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 940233099429005296836613 176293706142938493156865)
            ·
              refine ⟨132220279607203869867649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176293706142938493156865 132220279607203869867649)
              ·
                refine ⟨99165209705402902400737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132220279607203869867649 99165209705402902400737)
                ·
                  refine ⟨74373907279052176800553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99165209705402902400737 74373907279052176800553)
                  ·
                    rfl

theorem cell20_162948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_162948 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162948 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162948 prefixEnd_162948 := by exact prefixLift 162948
  have htrace : WordTrace (prefixWord ++ tailWord_162948) baseStart_162948 baseEnd_162948 := by
    simpa [prefixWord, tailWord_162948, baseEnd_162948] using wordTrace_append hprefix tailTrace_162948
  have hstable : (prefixWord ++ tailWord_162948).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162948).length < 2 ^ (prefixWord ++ tailWord_162948).sum := by decide
  have hdescent : baseEnd_162948 < baseStart_162948 := by decide
  rcases family_descends (prefixWord ++ tailWord_162948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162956 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 8]
def baseStart_162956 : Nat := 118140960795 + 162956 * 2 ^ 59
def prefixEnd_162956 : Nat := 4983230072969 + 3 ^ 40 * 162956 * 2
def baseEnd_162956 : Nat := 74377558697039704533853

theorem tailTrace_162956 : CollatzResearch.WordTrace tailWord_162956 prefixEnd_162956 74377558697039704533853 := by
  unfold tailWord_162956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971746798822858757098361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3962329065097145009464481 2971746798822858757098361)
  ·
    refine ⟨2228810099117144067823771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2971746798822858757098361 2228810099117144067823771)
    ·
      refine ⟨3343215148675716101735657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228810099117144067823771 3343215148675716101735657)
      ·
        refine ⟨2507411361506787076301743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3343215148675716101735657 2507411361506787076301743)
        ·
          refine ⟨3761117042260180614452615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507411361506787076301743 3761117042260180614452615)
          ·
            refine ⟨5641675563390270921678923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761117042260180614452615 5641675563390270921678923)
            ·
              refine ⟨8462513345085406382518385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5641675563390270921678923 8462513345085406382518385)
              ·
                refine ⟨6346885008814054786888789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8462513345085406382518385 6346885008814054786888789)
                ·
                  refine ⟨74377558697039704533853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6346885008814054786888789 74377558697039704533853)
                  ·
                    rfl

theorem cell20_162956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_162956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162956 prefixEnd_162956 := by exact prefixLift 162956
  have htrace : WordTrace (prefixWord ++ tailWord_162956) baseStart_162956 baseEnd_162956 := by
    simpa [prefixWord, tailWord_162956, baseEnd_162956] using wordTrace_append hprefix tailTrace_162956
  have hstable : (prefixWord ++ tailWord_162956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162956).length < 2 ^ (prefixWord ++ tailWord_162956).sum := by decide
  have hdescent : baseEnd_162956 < baseStart_162956 := by decide
  rcases family_descends (prefixWord ++ tailWord_162956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162973 : List Nat := [1, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_162973 : Nat := 118140960795 + 162973 * 2 ^ 59
def prefixEnd_162973 : Nat := 4983230072969 + 3 ^ 40 * 162973 * 2
def baseEnd_162973 : Nat := 74385317960263200967117

theorem tailTrace_162973 : CollatzResearch.WordTrace tailWord_162973 prefixEnd_162973 74385317960263200967117 := by
  unfold tailWord_162973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5944113638584129417565573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3962742425722752945043715 5944113638584129417565573)
  ·
    refine ⟨1114521307234524265793545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5944113638584129417565573 1114521307234524265793545)
    ·
      refine ⟨835890980425893199345159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1114521307234524265793545 835890980425893199345159)
      ·
        refine ⟨1253836470638839799017739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 835890980425893199345159 1253836470638839799017739)
        ·
          refine ⟨1880754705958259698526609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253836470638839799017739 1880754705958259698526609)
          ·
            refine ⟨1410566029468694773894957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880754705958259698526609 1410566029468694773894957)
            ·
              refine ⟨528962261050760540210609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1410566029468694773894957 528962261050760540210609)
              ·
                refine ⟨396721695788070405157957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 528962261050760540210609 396721695788070405157957)
                ·
                  refine ⟨74385317960263200967117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 396721695788070405157957 74385317960263200967117)
                  ·
                    rfl

theorem cell20_162973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_162973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162973 prefixEnd_162973 := by exact prefixLift 162973
  have htrace : WordTrace (prefixWord ++ tailWord_162973) baseStart_162973 baseEnd_162973 := by
    simpa [prefixWord, tailWord_162973, baseEnd_162973] using wordTrace_append hprefix tailTrace_162973
  have hstable : (prefixWord ++ tailWord_162973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162973).length < 2 ^ (prefixWord ++ tailWord_162973).sum := by decide
  have hdescent : baseEnd_162973 < baseStart_162973 := by decide
  rcases family_descends (prefixWord ++ tailWord_162973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_162986 : List Nat := [3, 1, 5, 1, 1, 2, 2, 3, 2]
def baseStart_162986 : Nat := 118140960795 + 162986 * 2 ^ 59
def prefixEnd_162986 : Nat := 4983230072969 + 3 ^ 40 * 162986 * 2
def baseEnd_162986 : Nat := 74391251514492933533731

theorem tailTrace_162986 : CollatzResearch.WordTrace tailWord_162986 prefixEnd_162986 74391251514492933533731 := by
  unfold tailWord_162986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486146946884258159447203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3963058525024688425192541 1486146946884258159447203)
  ·
    refine ⟨2229220420326387239170805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1486146946884258159447203 2229220420326387239170805)
    ·
      refine ⟨208989414405598803672263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2229220420326387239170805 208989414405598803672263)
      ·
        refine ⟨313484121608398205508395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208989414405598803672263 313484121608398205508395)
        ·
          refine ⟨470226182412597308262593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313484121608398205508395 470226182412597308262593)
          ·
            refine ⟨352669636809447981196945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470226182412597308262593 352669636809447981196945)
            ·
              refine ⟨264502227607085985897709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 352669636809447981196945 264502227607085985897709)
              ·
                refine ⟨99188335352657244711641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264502227607085985897709 99188335352657244711641)
                ·
                  refine ⟨74391251514492933533731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99188335352657244711641 74391251514492933533731)
                  ·
                    rfl

theorem cell20_162986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 3, 2].length) (baseStart_162986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_162986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_162986 prefixEnd_162986 := by exact prefixLift 162986
  have htrace : WordTrace (prefixWord ++ tailWord_162986) baseStart_162986 baseEnd_162986 := by
    simpa [prefixWord, tailWord_162986, baseEnd_162986] using wordTrace_append hprefix tailTrace_162986
  have hstable : (prefixWord ++ tailWord_162986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_162986).length < 2 ^ (prefixWord ++ tailWord_162986).sum := by decide
  have hdescent : baseEnd_162986 < baseStart_162986 := by decide
  rcases family_descends (prefixWord ++ tailWord_162986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163004 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 5]
def baseStart_163004 : Nat := 118140960795 + 163004 * 2 ^ 59
def prefixEnd_163004 : Nat := 4983230072969 + 3 ^ 40 * 163004 * 2
def baseEnd_163004 : Nat := 74399467204964870933657

theorem tailTrace_163004 : CollatzResearch.WordTrace tailWord_163004 prefixEnd_163004 74399467204964870933657 := by
  unfold tailWord_163004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2972622150735910855972033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3963496200981214474629377 2972622150735910855972033)
  ·
    refine ⟨2229466613051933141979025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2972622150735910855972033 2229466613051933141979025)
    ·
      refine ⟨1672099959788949856484269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2229466613051933141979025 1672099959788949856484269)
      ·
        refine ⟨627037484920856196181601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1672099959788949856484269 627037484920856196181601)
        ·
          refine ⟨470278113690642147136201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627037484920856196181601 470278113690642147136201)
          ·
            refine ⟨352708585267981610352151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 470278113690642147136201 352708585267981610352151)
            ·
              refine ⟨529062877901972415528227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352708585267981610352151 529062877901972415528227)
              ·
                refine ⟨793594316852958623292341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 529062877901972415528227 793594316852958623292341)
                ·
                  refine ⟨74399467204964870933657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 793594316852958623292341 74399467204964870933657)
                  ·
                    rfl

theorem cell20_163004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_163004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163004 prefixEnd_163004 := by exact prefixLift 163004
  have htrace : WordTrace (prefixWord ++ tailWord_163004) baseStart_163004 baseEnd_163004 := by
    simpa [prefixWord, tailWord_163004, baseEnd_163004] using wordTrace_append hprefix tailTrace_163004
  have hstable : (prefixWord ++ tailWord_163004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163004).length < 2 ^ (prefixWord ++ tailWord_163004).sum := by decide
  have hdescent : baseEnd_163004 < baseStart_163004 := by decide
  rcases family_descends (prefixWord ++ tailWord_163004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163076 : List Nat := [2, 3, 2, 2, 2, 3, 2, 1, 3]
def baseStart_163076 : Nat := 118140960795 + 163076 * 2 ^ 59
def prefixEnd_163076 : Nat := 4983230072969 + 3 ^ 40 * 163076 * 2
def baseEnd_163076 : Nat := 74432329966852620533363

theorem tailTrace_163076 : CollatzResearch.WordTrace tailWord_163076 prefixEnd_163076 74432329966852620533363 := by
  unfold tailWord_163076
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973935178605489004282541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3965246904807318672376721 2973935178605489004282541)
  ·
    refine ⟨1115225691977058376605953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2973935178605489004282541 1115225691977058376605953)
    ·
      refine ⟨836419268982793782454465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1115225691977058376605953 836419268982793782454465)
      ·
        refine ⟨627314451737095336840849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 836419268982793782454465 627314451737095336840849)
        ·
          refine ⟨470485838802821502630637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627314451737095336840849 470485838802821502630637)
          ·
            refine ⟨176432189551058063486489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470485838802821502630637 176432189551058063486489)
            ·
              refine ⟨132324142163293547614867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176432189551058063486489 132324142163293547614867)
              ·
                refine ⟨198486213244940321422301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132324142163293547614867 198486213244940321422301)
                ·
                  refine ⟨74432329966852620533363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198486213244940321422301 74432329966852620533363)
                  ·
                    rfl

theorem cell20_163076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_163076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163076 prefixEnd_163076 := by exact prefixLift 163076
  have htrace : WordTrace (prefixWord ++ tailWord_163076) baseStart_163076 baseEnd_163076 := by
    simpa [prefixWord, tailWord_163076, baseEnd_163076] using wordTrace_append hprefix tailTrace_163076
  have hstable : (prefixWord ++ tailWord_163076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163076).length < 2 ^ (prefixWord ++ tailWord_163076).sum := by decide
  have hdescent : baseEnd_163076 < baseStart_163076 := by decide
  rcases family_descends (prefixWord ++ tailWord_163076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163117 : List Nat := [1, 5, 3, 1, 1, 3, 2, 2, 2]
def baseStart_163117 : Nat := 118140960795 + 163117 * 2 ^ 59
def prefixEnd_163117 : Nat := 4983230072969 + 3 ^ 40 * 163117 * 2
def baseEnd_163117 : Nat := 74451043484038700166529

theorem tailTrace_163117 : CollatzResearch.WordTrace tailWord_163117 prefixEnd_163117 74451043484038700166529 := by
  unfold tailWord_163117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949365750062442010807605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3966243833374961340538403 5949365750062442010807605)
  ·
    refine ⟨557753039068353938513213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5949365750062442010807605 557753039068353938513213)
    ·
      refine ⟨209157389650632726942455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 557753039068353938513213 209157389650632726942455)
      ·
        refine ⟨313736084475949090413683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209157389650632726942455 313736084475949090413683)
        ·
          refine ⟨470604126713923635620525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313736084475949090413683 470604126713923635620525)
          ·
            refine ⟨176476547517721363357697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470604126713923635620525 176476547517721363357697)
            ·
              refine ⟨132357410638291022518273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176476547517721363357697 132357410638291022518273)
              ·
                refine ⟨99268057978718266888705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132357410638291022518273 99268057978718266888705)
                ·
                  refine ⟨74451043484038700166529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99268057978718266888705 74451043484038700166529)
                  ·
                    rfl

theorem cell20_163117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_163117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163117 prefixEnd_163117 := by exact prefixLift 163117
  have htrace : WordTrace (prefixWord ++ tailWord_163117) baseStart_163117 baseEnd_163117 := by
    simpa [prefixWord, tailWord_163117, baseEnd_163117] using wordTrace_append hprefix tailTrace_163117
  have hstable : (prefixWord ++ tailWord_163117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163117).length < 2 ^ (prefixWord ++ tailWord_163117).sum := by decide
  have hdescent : baseEnd_163117 < baseStart_163117 := by decide
  rcases family_descends (prefixWord ++ tailWord_163117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163121 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 2]
def baseStart_163121 : Nat := 118140960795 + 163121 * 2 ^ 59
def prefixEnd_163121 : Nat := 4983230072969 + 3 ^ 40 * 163121 * 2
def baseEnd_163121 : Nat := 74452869193032464033179

theorem tailTrace_163121 : CollatzResearch.WordTrace tailWord_163121 prefixEnd_163121 74452869193032464033179 := by
  unfold tailWord_163121
  simp only [CollatzResearch.WordTrace]
  refine ⟨5949511642047950693953217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3966341094698633795968811 5949511642047950693953217)
  ·
    refine ⟨4462133731535963020464913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5949511642047950693953217 4462133731535963020464913)
    ·
      refine ⟨3346600298651972265348685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4462133731535963020464913 3346600298651972265348685)
      ·
        refine ⟨1254975111994489599505757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3346600298651972265348685 1254975111994489599505757)
        ·
          refine ⟨470615666997933599814659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1254975111994489599505757 470615666997933599814659)
          ·
            refine ⟨705923500496900399721989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470615666997933599814659 705923500496900399721989)
            ·
              refine ⟨132360656343168824947873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 705923500496900399721989 132360656343168824947873)
              ·
                refine ⟨99270492257376618710905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132360656343168824947873 99270492257376618710905)
                ·
                  refine ⟨74452869193032464033179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99270492257376618710905 74452869193032464033179)
                  ·
                    rfl

theorem cell20_163121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 2].length) (baseStart_163121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163121 prefixEnd_163121 := by exact prefixLift 163121
  have htrace : WordTrace (prefixWord ++ tailWord_163121) baseStart_163121 baseEnd_163121 := by
    simpa [prefixWord, tailWord_163121, baseEnd_163121] using wordTrace_append hprefix tailTrace_163121
  have hstable : (prefixWord ++ tailWord_163121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163121).length < 2 ^ (prefixWord ++ tailWord_163121).sum := by decide
  have hdescent : baseEnd_163121 < baseStart_163121 := by decide
  rcases family_descends (prefixWord ++ tailWord_163121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163132 : List Nat := [2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_163132 : Nat := 118140960795 + 163132 * 2 ^ 59
def prefixEnd_163132 : Nat := 4983230072969 + 3 ^ 40 * 163132 * 2
def baseEnd_163132 : Nat := 24819296630921771555489

theorem tailTrace_163132 : CollatzResearch.WordTrace tailWord_163132 prefixEnd_163132 24819296630921771555489 := by
  unfold tailWord_163132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974956422504049786301825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3966608563338733048402433 2974956422504049786301825)
  ·
    refine ⟨2231217316878037339726369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2974956422504049786301825 2231217316878037339726369)
    ·
      refine ⟨1673412987658528004794777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2231217316878037339726369 1673412987658528004794777)
      ·
        refine ⟨1255059740743896003596083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1673412987658528004794777 1255059740743896003596083)
        ·
          refine ⟨1882589611115844005394125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255059740743896003596083 1882589611115844005394125)
          ·
            refine ⟨705971104168441502022797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1882589611115844005394125 705971104168441502022797)
            ·
              refine ⟨264739164063165563258549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 705971104168441502022797 264739164063165563258549)
              ·
                refine ⟨24819296630921771555489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 264739164063165563258549 24819296630921771555489)
                ·
                  rfl

theorem cell20_163132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_163132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163132 prefixEnd_163132 := by exact prefixLift 163132
  have htrace : WordTrace (prefixWord ++ tailWord_163132) baseStart_163132 baseEnd_163132 := by
    simpa [prefixWord, tailWord_163132, baseEnd_163132] using wordTrace_append hprefix tailTrace_163132
  have hstable : (prefixWord ++ tailWord_163132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163132).length < 2 ^ (prefixWord ++ tailWord_163132).sum := by decide
  have hdescent : baseEnd_163132 < baseStart_163132 := by decide
  rcases family_descends (prefixWord ++ tailWord_163132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163170 : List Nat := [3, 3, 2, 1, 1, 1, 9]
def baseStart_163170 : Nat := 118140960795 + 163170 * 2 ^ 59
def prefixEnd_163170 : Nat := 4983230072969 + 3 ^ 40 * 163170 * 2
def baseEnd_163170 : Nat := 8275026014245119044405

theorem tailTrace_163170 : CollatzResearch.WordTrace tailWord_163170 prefixEnd_163170 8275026014245119044405 := by
  unfold tailWord_163170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487824704717608015621741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3967532545913621374991309 1487824704717608015621741)
  ·
    refine ⟨557934264269103005858153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1487824704717608015621741 557934264269103005858153)
    ·
      refine ⟨418450698201827254393615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 557934264269103005858153 418450698201827254393615)
      ·
        refine ⟨627676047302740881590423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 418450698201827254393615 627676047302740881590423)
        ·
          refine ⟨941514070954111322385635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627676047302740881590423 941514070954111322385635)
          ·
            refine ⟨1412271106431166983578453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941514070954111322385635 1412271106431166983578453)
            ·
              refine ⟨8275026014245119044405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1412271106431166983578453 8275026014245119044405)
              ·
                rfl

theorem cell20_163170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_163170 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163170 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163170 prefixEnd_163170 := by exact prefixLift 163170
  have htrace : WordTrace (prefixWord ++ tailWord_163170) baseStart_163170 baseEnd_163170 := by
    simpa [prefixWord, tailWord_163170, baseEnd_163170] using wordTrace_append hprefix tailTrace_163170
  have hstable : (prefixWord ++ tailWord_163170).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163170).length < 2 ^ (prefixWord ++ tailWord_163170).sum := by decide
  have hdescent : baseEnd_163170 < baseStart_163170 := by decide
  rcases family_descends (prefixWord ++ tailWord_163170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163177 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_163177 : Nat := 118140960795 + 163177 * 2 ^ 59
def prefixEnd_163177 : Nat := 4983230072969 + 3 ^ 40 * 163177 * 2
def baseEnd_163177 : Nat := 74478429118945158166283

theorem tailTrace_163177 : CollatzResearch.WordTrace tailWord_163177 prefixEnd_163177 74478429118945158166283 := by
  unfold tailWord_163177
  simp only [CollatzResearch.WordTrace]
  refine ⟨5951554129845072257991785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3967702753230048171994523 5951554129845072257991785)
  ·
    refine ⟨4463665597383804193493839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5951554129845072257991785 4463665597383804193493839)
    ·
      refine ⟨6695498396075706290240759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4463665597383804193493839 6695498396075706290240759)
      ·
        refine ⟨10043247594113559435361139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6695498396075706290240759 10043247594113559435361139)
        ·
          refine ⟨15064871391170339153041709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10043247594113559435361139 15064871391170339153041709)
          ·
            refine ⟨5649326771688877182390641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15064871391170339153041709 5649326771688877182390641)
            ·
              refine ⟨4236995078766657886792981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5649326771688877182390641 4236995078766657886792981)
              ·
                refine ⟨198609144317187088443421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4236995078766657886792981 198609144317187088443421)
                ·
                  refine ⟨74478429118945158166283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198609144317187088443421 74478429118945158166283)
                  ·
                    rfl

theorem cell20_163177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_163177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163177 prefixEnd_163177 := by exact prefixLift 163177
  have htrace : WordTrace (prefixWord ++ tailWord_163177) baseStart_163177 baseEnd_163177 := by
    simpa [prefixWord, tailWord_163177, baseEnd_163177] using wordTrace_append hprefix tailTrace_163177
  have hstable : (prefixWord ++ tailWord_163177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163177).length < 2 ^ (prefixWord ++ tailWord_163177).sum := by decide
  have hdescent : baseEnd_163177 < baseStart_163177 := by decide
  rcases family_descends (prefixWord ++ tailWord_163177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163180 : List Nat := [2, 2, 1, 1, 5, 1, 2, 4, 2]
def baseStart_163180 : Nat := 118140960795 + 163180 * 2 ^ 59
def prefixEnd_163180 : Nat := 4983230072969 + 3 ^ 40 * 163180 * 2
def baseEnd_163180 : Nat := 74479798400690481066271

theorem tailTrace_163180 : CollatzResearch.WordTrace tailWord_163180 prefixEnd_163180 74479798400690481066271 := by
  unfold tailWord_163180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975831774417101885175497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3967775699222802513567329 2975831774417101885175497)
  ·
    refine ⟨2231873830812826413881623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2975831774417101885175497 2231873830812826413881623)
    ·
      refine ⟨3347810746219239620822435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231873830812826413881623 3347810746219239620822435)
      ·
        refine ⟨5021716119328859431233653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3347810746219239620822435 5021716119328859431233653)
        ·
          refine ⟨470785886187080571678155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5021716119328859431233653 470785886187080571678155)
          ·
            refine ⟨706178829280620857517233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470785886187080571678155 706178829280620857517233)
            ·
              refine ⟨529634121960465643137925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706178829280620857517233 529634121960465643137925)
              ·
                refine ⟨99306397867587308088361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529634121960465643137925 99306397867587308088361)
                ·
                  refine ⟨74479798400690481066271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99306397867587308088361 74479798400690481066271)
                  ·
                    rfl

theorem cell20_163180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 4, 2].length) (baseStart_163180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163180 prefixEnd_163180 := by exact prefixLift 163180
  have htrace : WordTrace (prefixWord ++ tailWord_163180) baseStart_163180 baseEnd_163180 := by
    simpa [prefixWord, tailWord_163180, baseEnd_163180] using wordTrace_append hprefix tailTrace_163180
  have hstable : (prefixWord ++ tailWord_163180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163180).length < 2 ^ (prefixWord ++ tailWord_163180).sum := by decide
  have hdescent : baseEnd_163180 < baseStart_163180 := by decide
  rcases family_descends (prefixWord ++ tailWord_163180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163191 : List Nat := [1, 1, 3, 1, 1, 2, 4, 7]
def baseStart_163191 : Nat := 118140960795 + 163191 * 2 ^ 59
def prefixEnd_163191 : Nat := 4983230072969 + 3 ^ 40 * 163191 * 2
def baseEnd_163191 : Nat := 24828273033474443899853

theorem tailTrace_163191 : CollatzResearch.WordTrace tailWord_163191 prefixEnd_163191 24828273033474443899853 := by
  unfold tailWord_163191
  simp only [CollatzResearch.WordTrace]
  refine ⟨5952064751794352649001427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3968043167862901766000951 5952064751794352649001427)
  ·
    refine ⟨8928097127691528973502141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5952064751794352649001427 8928097127691528973502141)
    ·
      refine ⟨3348036422884323365063303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8928097127691528973502141 3348036422884323365063303)
      ·
        refine ⟨5022054634326485047594955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3348036422884323365063303 5022054634326485047594955)
        ·
          refine ⟨7533081951489727571392433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5022054634326485047594955 7533081951489727571392433)
          ·
            refine ⟨5649811463617295678544325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7533081951489727571392433 5649811463617295678544325)
            ·
              refine ⟨1059339649428242939727061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5649811463617295678544325 1059339649428242939727061)
              ·
                refine ⟨24828273033474443899853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1059339649428242939727061 24828273033474443899853)
                ·
                  rfl

theorem cell20_163191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 7].length) (baseStart_163191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163191 prefixEnd_163191 := by exact prefixLift 163191
  have htrace : WordTrace (prefixWord ++ tailWord_163191) baseStart_163191 baseEnd_163191 := by
    simpa [prefixWord, tailWord_163191, baseEnd_163191] using wordTrace_append hprefix tailTrace_163191
  have hstable : (prefixWord ++ tailWord_163191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163191).length < 2 ^ (prefixWord ++ tailWord_163191).sum := by decide
  have hdescent : baseEnd_163191 < baseStart_163191 := by decide
  rcases family_descends (prefixWord ++ tailWord_163191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163208 : List Nat := [2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_163208 : Nat := 118140960795 + 163208 * 2 ^ 59
def prefixEnd_163208 : Nat := 4983230072969 + 3 ^ 40 * 163208 * 2
def baseEnd_163208 : Nat := 24830859454548942710941

theorem tailTrace_163208 : CollatzResearch.WordTrace tailWord_163208 prefixEnd_163208 24830859454548942710941 := by
  unfold tailWord_163208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976342396366382276185139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3968456528488509701580185 2976342396366382276185139)
  ·
    refine ⟨4464513594549573414277709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976342396366382276185139 4464513594549573414277709)
    ·
      refine ⟨1674192597956090030354141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4464513594549573414277709 1674192597956090030354141)
      ·
        refine ⟨627822224233533761382803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1674192597956090030354141 627822224233533761382803)
        ·
          refine ⟨941733336350300642074205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627822224233533761382803 941733336350300642074205)
          ·
            refine ⟨353150001131362740777827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 941733336350300642074205 353150001131362740777827)
            ·
              refine ⟨529725001697044111166741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353150001131362740777827 529725001697044111166741)
              ·
                refine ⟨24830859454548942710941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 529725001697044111166741 24830859454548942710941)
                ·
                  rfl

theorem cell20_163208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_163208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163208 prefixEnd_163208 := by exact prefixLift 163208
  have htrace : WordTrace (prefixWord ++ tailWord_163208) baseStart_163208 baseEnd_163208 := by
    simpa [prefixWord, tailWord_163208, baseEnd_163208] using wordTrace_append hprefix tailTrace_163208
  have hstable : (prefixWord ++ tailWord_163208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163208).length < 2 ^ (prefixWord ++ tailWord_163208).sum := by decide
  have hdescent : baseEnd_163208 < baseStart_163208 := by decide
  rcases family_descends (prefixWord ++ tailWord_163208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163214 : List Nat := [4, 1, 1, 4, 2, 2, 1, 3, 2]
def baseStart_163214 : Nat := 118140960795 + 163214 * 2 ^ 59
def prefixEnd_163214 : Nat := 4983230072969 + 3 ^ 40 * 163214 * 2
def baseEnd_163214 : Nat := 74495316927137473932799

theorem tailTrace_163214 : CollatzResearch.WordTrace tailWord_163214 prefixEnd_163214 74495316927137473932799 := by
  unfold tailWord_163214
  simp only [CollatzResearch.WordTrace]
  refine ⟨744112953838878447136087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3968602420474018384725797 744112953838878447136087)
  ·
    refine ⟨1116169430758317670704131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744112953838878447136087 1116169430758317670704131)
    ·
      refine ⟨1674254146137476506056197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1116169430758317670704131 1674254146137476506056197)
      ·
        refine ⟨313922652400776844885537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1674254146137476506056197 313922652400776844885537)
        ·
          refine ⟨235441989300582633664153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313922652400776844885537 235441989300582633664153)
          ·
            refine ⟨176581491975436975248115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235441989300582633664153 176581491975436975248115)
            ·
              refine ⟨264872237963155462872173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176581491975436975248115 264872237963155462872173)
              ·
                refine ⟨99327089236183298577065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264872237963155462872173 99327089236183298577065)
                ·
                  refine ⟨74495316927137473932799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99327089236183298577065 74495316927137473932799)
                  ·
                    rfl

theorem cell20_163214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 2].length) (baseStart_163214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163214 prefixEnd_163214 := by exact prefixLift 163214
  have htrace : WordTrace (prefixWord ++ tailWord_163214) baseStart_163214 baseEnd_163214 := by
    simpa [prefixWord, tailWord_163214, baseEnd_163214] using wordTrace_append hprefix tailTrace_163214
  have hstable : (prefixWord ++ tailWord_163214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163214).length < 2 ^ (prefixWord ++ tailWord_163214).sum := by decide
  have hdescent : baseEnd_163214 < baseStart_163214 := by decide
  rcases family_descends (prefixWord ++ tailWord_163214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163267 : List Nat := [1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_163267 : Nat := 118140960795 + 163267 * 2 ^ 59
def prefixEnd_163267 : Nat := 4983230072969 + 3 ^ 40 * 163267 * 2
def baseEnd_163267 : Nat := 24839835857101615055305

theorem tailTrace_163267 : CollatzResearch.WordTrace tailWord_163267 prefixEnd_163267 24839835857101615055305 := by
  unfold tailWord_163267
  simp only [CollatzResearch.WordTrace]
  refine ⟨5954836699519017628768055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3969891133012678419178703 5954836699519017628768055)
  ·
    refine ⟨8932255049278526443152083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5954836699519017628768055 8932255049278526443152083)
    ·
      refine ⟨13398382573917789664728125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8932255049278526443152083 13398382573917789664728125)
      ·
        refine ⟨5024393465219171124273047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13398382573917789664728125 5024393465219171124273047)
        ·
          refine ⟨7536590197828756686409571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5024393465219171124273047 7536590197828756686409571)
          ·
            refine ⟨11304885296743135029614357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7536590197828756686409571 11304885296743135029614357)
            ·
              refine ⟨529916498284834454513173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11304885296743135029614357 529916498284834454513173)
              ·
                refine ⟨24839835857101615055305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 529916498284834454513173 24839835857101615055305)
                ·
                  rfl

theorem cell20_163267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_163267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163267 prefixEnd_163267 := by exact prefixLift 163267
  have htrace : WordTrace (prefixWord ++ tailWord_163267) baseStart_163267 baseEnd_163267 := by
    simpa [prefixWord, tailWord_163267, baseEnd_163267] using wordTrace_append hprefix tailTrace_163267
  have hstable : (prefixWord ++ tailWord_163267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163267).length < 2 ^ (prefixWord ++ tailWord_163267).sum := by decide
  have hdescent : baseEnd_163267 < baseStart_163267 := by decide
  rcases family_descends (prefixWord ++ tailWord_163267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163284 : List Nat := [2, 4, 1, 2, 3, 8]
def baseStart_163284 : Nat := 118140960795 + 163284 * 2 ^ 59
def prefixEnd_163284 : Nat := 4983230072969 + 3 ^ 40 * 163284 * 2
def baseEnd_163284 : Nat := 2760269142019568207377

theorem tailTrace_163284 : CollatzResearch.WordTrace tailWord_163284 prefixEnd_163284 2760269142019568207377 := by
  unfold tailWord_163284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2977728370228714766068453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3970304493638286354757937 2977728370228714766068453)
  ·
    refine ⟨558324069417884018637835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2977728370228714766068453 558324069417884018637835)
    ·
      refine ⟨837486104126826027956753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 558324069417884018637835 837486104126826027956753)
      ·
        refine ⟨628114578095119520967565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 837486104126826027956753 628114578095119520967565)
        ·
          refine ⟨235542966785669820362837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 628114578095119520967565 235542966785669820362837)
          ·
            refine ⟨2760269142019568207377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 235542966785669820362837 2760269142019568207377)
            ·
              rfl

theorem cell20_163284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 8].length) (baseStart_163284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163284 prefixEnd_163284 := by exact prefixLift 163284
  have htrace : WordTrace (prefixWord ++ tailWord_163284) baseStart_163284 baseEnd_163284 := by
    simpa [prefixWord, tailWord_163284, baseEnd_163284] using wordTrace_append hprefix tailTrace_163284
  have hstable : (prefixWord ++ tailWord_163284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163284).length < 2 ^ (prefixWord ++ tailWord_163284).sum := by decide
  have hdescent : baseEnd_163284 < baseStart_163284 := by decide
  rcases family_descends (prefixWord ++ tailWord_163284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163301 : List Nat := [1, 3, 1, 5, 1, 3, 1, 5]
def baseStart_163301 : Nat := 118140960795 + 163301 * 2 ^ 59
def prefixEnd_163301 : Nat := 4983230072969 + 3 ^ 40 * 163301 * 2
def baseEnd_163301 : Nat := 24845008699250612677481

theorem tailTrace_163301 : CollatzResearch.WordTrace tailWord_163301 prefixEnd_163301 24845008699250612677481 := by
  unfold tailWord_163301
  simp only [CollatzResearch.WordTrace]
  refine ⟨5956076781395841435505757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3970717854263894290337171 5956076781395841435505757)
  ·
    refine ⟨2233528793023440538314659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5956076781395841435505757 2233528793023440538314659)
    ·
      refine ⟨3350293189535160807471989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233528793023440538314659 3350293189535160807471989)
      ·
        refine ⟨314089986518921325700499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3350293189535160807471989 314089986518921325700499)
        ·
          refine ⟨471134979778381988550749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314089986518921325700499 471134979778381988550749)
          ·
            refine ⟨176675617416893245706531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 471134979778381988550749 176675617416893245706531)
            ·
              refine ⟨265013426125339868559797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176675617416893245706531 265013426125339868559797)
              ·
                refine ⟨24845008699250612677481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265013426125339868559797 24845008699250612677481)
                ·
                  rfl

theorem cell20_163301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 5].length) (baseStart_163301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163301 prefixEnd_163301 := by exact prefixLift 163301
  have htrace : WordTrace (prefixWord ++ tailWord_163301) baseStart_163301 baseEnd_163301 := by
    simpa [prefixWord, tailWord_163301, baseEnd_163301] using wordTrace_append hprefix tailTrace_163301
  have hstable : (prefixWord ++ tailWord_163301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163301).length < 2 ^ (prefixWord ++ tailWord_163301).sum := by decide
  have hdescent : baseEnd_163301 < baseStart_163301 := by decide
  rcases family_descends (prefixWord ++ tailWord_163301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163322 : List Nat := [3, 1, 1, 1, 1, 2, 7, 4]
def baseStart_163322 : Nat := 118140960795 + 163322 * 2 ^ 59
def prefixEnd_163322 : Nat := 4983230072969 + 3 ^ 40 * 163322 * 2
def baseEnd_163322 : Nat := 24848203689989699444119

theorem tailTrace_163322 : CollatzResearch.WordTrace tailWord_163322 prefixEnd_163322 24848203689989699444119 := by
  unfold tailWord_163322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1489210678579940505505055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3971228476213174681346813 1489210678579940505505055)
  ·
    refine ⟨2233816017869910758257583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1489210678579940505505055 2233816017869910758257583)
    ·
      refine ⟨3350724026804866137386375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2233816017869910758257583 3350724026804866137386375)
      ·
        refine ⟨5026086040207299206079563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3350724026804866137386375 5026086040207299206079563)
        ·
          refine ⟨7539129060310948809119345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5026086040207299206079563 7539129060310948809119345)
          ·
            refine ⟨5654346795233211606839509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7539129060310948809119345 5654346795233211606839509)
            ·
              refine ⟨132523753013278397035301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5654346795233211606839509 132523753013278397035301)
              ·
                refine ⟨24848203689989699444119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132523753013278397035301 24848203689989699444119)
                ·
                  rfl

theorem cell20_163322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_163322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163322 prefixEnd_163322 := by exact prefixLift 163322
  have htrace : WordTrace (prefixWord ++ tailWord_163322) baseStart_163322 baseEnd_163322 := by
    simpa [prefixWord, tailWord_163322, baseEnd_163322] using wordTrace_append hprefix tailTrace_163322
  have hstable : (prefixWord ++ tailWord_163322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163322).length < 2 ^ (prefixWord ++ tailWord_163322).sum := by decide
  have hdescent : baseEnd_163322 < baseStart_163322 := by decide
  rcases family_descends (prefixWord ++ tailWord_163322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163342 : List Nat := [4, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_163342 : Nat := 118140960795 + 163342 * 2 ^ 59
def prefixEnd_163342 : Nat := 4983230072969 + 3 ^ 40 * 163342 * 2
def baseEnd_163342 : Nat := 74553739614937917665609

theorem tailTrace_163342 : CollatzResearch.WordTrace tailWord_163342 prefixEnd_163342 74553739614937917665609 := by
  unfold tailWord_163342
  simp only [CollatzResearch.WordTrace]
  refine ⟨744696521780913179718535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3971714782831536958498853 744696521780913179718535)
  ·
    refine ⟨1117044782671369769577803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 744696521780913179718535 1117044782671369769577803)
    ·
      refine ⟨1675567174007054654366705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1117044782671369769577803 1675567174007054654366705)
      ·
        refine ⟨1256675380505290990775029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1675567174007054654366705 1256675380505290990775029)
        ·
          refine ⟨117813316922371030385159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1256675380505290990775029 117813316922371030385159)
          ·
            refine ⟨176719975383556545577739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117813316922371030385159 176719975383556545577739)
            ·
              refine ⟨265079963075334818366609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176719975383556545577739 265079963075334818366609)
              ·
                refine ⟨198809972306501113774957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265079963075334818366609 198809972306501113774957)
                ·
                  refine ⟨74553739614937917665609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198809972306501113774957 74553739614937917665609)
                  ·
                    rfl

theorem cell20_163342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_163342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163342 prefixEnd_163342 := by exact prefixLift 163342
  have htrace : WordTrace (prefixWord ++ tailWord_163342) baseStart_163342 baseEnd_163342 := by
    simpa [prefixWord, tailWord_163342, baseEnd_163342] using wordTrace_append hprefix tailTrace_163342
  have hstable : (prefixWord ++ tailWord_163342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163342).length < 2 ^ (prefixWord ++ tailWord_163342).sum := by decide
  have hdescent : baseEnd_163342 < baseStart_163342 := by decide
  rcases family_descends (prefixWord ++ tailWord_163342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163363 : List Nat := [1, 1, 1, 4, 5, 1, 3, 1, 3]
def baseStart_163363 : Nat := 118140960795 + 163363 * 2 ^ 59
def prefixEnd_163363 : Nat := 4983230072969 + 3 ^ 40 * 163363 * 2
def baseEnd_163363 : Nat := 74563324587155177965523

theorem tailTrace_163363 : CollatzResearch.WordTrace tailWord_163363 prefixEnd_163363 74563324587155177965523 := by
  unfold tailWord_163363
  simp only [CollatzResearch.WordTrace]
  refine ⟨5958338107171226024262743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3972225404780817349508495 5958338107171226024262743)
  ·
    refine ⟨8937507160756839036394115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5958338107171226024262743 8937507160756839036394115)
    ·
      refine ⟨13406260741135258554591173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8937507160756839036394115 13406260741135258554591173)
      ·
        refine ⟨2513673888962860978985845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13406260741135258554591173 2513673888962860978985845)
        ·
          refine ⟨235656927090268216779923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2513673888962860978985845 235656927090268216779923)
          ·
            refine ⟨353485390635402325169885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235656927090268216779923 353485390635402325169885)
            ·
              refine ⟨132557021488275871938707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 353485390635402325169885 132557021488275871938707)
              ·
                refine ⟨198835532232413807908061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132557021488275871938707 198835532232413807908061)
                ·
                  refine ⟨74563324587155177965523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198835532232413807908061 74563324587155177965523)
                  ·
                    rfl

theorem cell20_163363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_163363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163363 prefixEnd_163363 := by exact prefixLift 163363
  have htrace : WordTrace (prefixWord ++ tailWord_163363) baseStart_163363 baseEnd_163363 := by
    simpa [prefixWord, tailWord_163363, baseEnd_163363] using wordTrace_append hprefix tailTrace_163363
  have hstable : (prefixWord ++ tailWord_163363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163363).length < 2 ^ (prefixWord ++ tailWord_163363).sum := by decide
  have hdescent : baseEnd_163363 < baseStart_163363 := by decide
  rcases family_descends (prefixWord ++ tailWord_163363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163408 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 2]
def baseStart_163408 : Nat := 118140960795 + 163408 * 2 ^ 59
def prefixEnd_163408 : Nat := 4983230072969 + 3 ^ 40 * 163408 * 2
def baseEnd_163408 : Nat := 74583863813335021465339

theorem tailTrace_163408 : CollatzResearch.WordTrace tailWord_163408 prefixEnd_163408 74583863813335021465339 := by
  unfold tailWord_163408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2979989696004099354825439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3973319594672132473100585 2979989696004099354825439)
  ·
    refine ⟨4469984544006149032238159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2979989696004099354825439 4469984544006149032238159)
    ·
      refine ⟨6704976816009223548357239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4469984544006149032238159 6704976816009223548357239)
      ·
        refine ⟨10057465224013835322535859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6704976816009223548357239 10057465224013835322535859)
        ·
          refine ⟨15086197836020752983803789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10057465224013835322535859 15086197836020752983803789)
          ·
            refine ⟨5657324188507782368926421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15086197836020752983803789 5657324188507782368926421)
            ·
              refine ⟨132593535668151149271713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5657324188507782368926421 132593535668151149271713)
              ·
                refine ⟨99445151751113361953785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132593535668151149271713 99445151751113361953785)
                ·
                  refine ⟨74583863813335021465339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99445151751113361953785 74583863813335021465339)
                  ·
                    rfl

theorem cell20_163408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_163408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163408 prefixEnd_163408 := by exact prefixLift 163408
  have htrace : WordTrace (prefixWord ++ tailWord_163408) baseStart_163408 baseEnd_163408 := by
    simpa [prefixWord, tailWord_163408, baseEnd_163408] using wordTrace_append hprefix tailTrace_163408
  have hstable : (prefixWord ++ tailWord_163408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163408).length < 2 ^ (prefixWord ++ tailWord_163408).sum := by decide
  have hdescent : baseEnd_163408 < baseStart_163408 := by decide
  rcases family_descends (prefixWord ++ tailWord_163408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163414 : List Nat := [5, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_163414 : Nat := 118140960795 + 163414 * 2 ^ 59
def prefixEnd_163414 : Nat := 4983230072969 + 3 ^ 40 * 163414 * 2
def baseEnd_163414 : Nat := 74586602376825667265315

theorem tailTrace_163414 : CollatzResearch.WordTrace tailWord_163414 prefixEnd_163414 74586602376825667265315 := by
  unfold tailWord_163414
  simp only [CollatzResearch.WordTrace]
  refine ⟨372512389374153858398081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3973465486657641156246197 372512389374153858398081)
  ·
    refine ⟨279384292030615393798561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 372512389374153858398081 279384292030615393798561)
    ·
      refine ⟨209538219022961545348921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279384292030615393798561 209538219022961545348921)
      ·
        refine ⟨157153664267221159011691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209538219022961545348921 157153664267221159011691)
        ·
          refine ⟨235730496400831738517537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157153664267221159011691 235730496400831738517537)
          ·
            refine ⟨176797872300623803888153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235730496400831738517537 176797872300623803888153)
            ·
              refine ⟨132598404225467852916115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176797872300623803888153 132598404225467852916115)
              ·
                refine ⟨198897606338201779374173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132598404225467852916115 198897606338201779374173)
                ·
                  refine ⟨74586602376825667265315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198897606338201779374173 74586602376825667265315)
                  ·
                    rfl

theorem cell20_163414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_163414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163414 prefixEnd_163414 := by exact prefixLift 163414
  have htrace : WordTrace (prefixWord ++ tailWord_163414) baseStart_163414 baseEnd_163414 := by
    simpa [prefixWord, tailWord_163414, baseEnd_163414] using wordTrace_append hprefix tailTrace_163414
  have hstable : (prefixWord ++ tailWord_163414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163414).length < 2 ^ (prefixWord ++ tailWord_163414).sum := by decide
  have hdescent : baseEnd_163414 < baseStart_163414 := by decide
  rcases family_descends (prefixWord ++ tailWord_163414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163457 : List Nat := [1, 2, 4, 2, 1, 10]
def baseStart_163457 : Nat := 118140960795 + 163457 * 2 ^ 59
def prefixEnd_163457 : Nat := 4983230072969 + 3 ^ 40 * 163457 * 2
def baseEnd_163457 : Nat := 2763193657352171438215

theorem tailTrace_163457 : CollatzResearch.WordTrace tailWord_163457 prefixEnd_163457 2763193657352171438215 := by
  unfold tailWord_163457
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961766568830680078184625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3974511045887120052123083 5961766568830680078184625)
  ·
    refine ⟨4471324926623010058638469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5961766568830680078184625 4471324926623010058638469)
    ·
      refine ⟨838373423741814385994713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4471324926623010058638469 838373423741814385994713)
      ·
        refine ⟨628780067806360789496035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 838373423741814385994713 628780067806360789496035)
        ·
          refine ⟨943170101709541184244053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628780067806360789496035 943170101709541184244053)
          ·
            refine ⟨2763193657352171438215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 943170101709541184244053 2763193657352171438215)
            ·
              rfl

theorem cell20_163457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 10].length) (baseStart_163457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163457 prefixEnd_163457 := by exact prefixLift 163457
  have htrace : WordTrace (prefixWord ++ tailWord_163457) baseStart_163457 baseEnd_163457 := by
    simpa [prefixWord, tailWord_163457, baseEnd_163457] using wordTrace_append hprefix tailTrace_163457
  have hstable : (prefixWord ++ tailWord_163457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163457).length < 2 ^ (prefixWord ++ tailWord_163457).sum := by decide
  have hdescent : baseEnd_163457 < baseStart_163457 := by decide
  rcases family_descends (prefixWord ++ tailWord_163457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163463 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 2]
def baseStart_163463 : Nat := 118140960795 + 163463 * 2 ^ 59
def prefixEnd_163463 : Nat := 4983230072969 + 3 ^ 40 * 163463 * 2
def baseEnd_163463 : Nat := 74608967311999274631781

theorem tailTrace_163463 : CollatzResearch.WordTrace tailWord_163463 prefixEnd_163463 74608967311999274631781 := by
  unfold tailWord_163463
  simp only [CollatzResearch.WordTrace]
  refine ⟨5961985406808943102903043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3974656937872628735268695 5961985406808943102903043)
  ·
    refine ⟨8942978110213414654354565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5961985406808943102903043 8942978110213414654354565)
    ·
      refine ⟨1676808395665015247691481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8942978110213414654354565 1676808395665015247691481)
      ·
        refine ⟨1257606296748761435768611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1676808395665015247691481 1257606296748761435768611)
        ·
          refine ⟨1886409445123142153652917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1257606296748761435768611 1886409445123142153652917)
          ·
            refine ⟨176850885480294576904961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1886409445123142153652917 176850885480294576904961)
            ·
              refine ⟨132638164110220932678721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176850885480294576904961 132638164110220932678721)
              ·
                refine ⟨99478623082665699509041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132638164110220932678721 99478623082665699509041)
                ·
                  refine ⟨74608967311999274631781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99478623082665699509041 74608967311999274631781)
                  ·
                    rfl

theorem cell20_163463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 2].length) (baseStart_163463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163463 prefixEnd_163463 := by exact prefixLift 163463
  have htrace : WordTrace (prefixWord ++ tailWord_163463) baseStart_163463 baseEnd_163463 := by
    simpa [prefixWord, tailWord_163463, baseEnd_163463] using wordTrace_append hprefix tailTrace_163463
  have hstable : (prefixWord ++ tailWord_163463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163463).length < 2 ^ (prefixWord ++ tailWord_163463).sum := by decide
  have hdescent : baseEnd_163463 < baseStart_163463 := by decide
  rcases family_descends (prefixWord ++ tailWord_163463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163467 : List Nat := [1, 1, 1, 1, 4, 1, 5, 4, 2]
def baseStart_163467 : Nat := 118140960795 + 163467 * 2 ^ 59
def prefixEnd_163467 : Nat := 4983230072969 + 3 ^ 40 * 163467 * 2
def baseEnd_163467 : Nat := 74610793020993038498431

theorem tailTrace_163467 : CollatzResearch.WordTrace tailWord_163467 prefixEnd_163467 74610793020993038498431 := by
  unfold tailWord_163467
  simp only [CollatzResearch.WordTrace]
  refine ⟨5962131298794451786048655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3974754199196301190699103 5962131298794451786048655)
  ·
    refine ⟨8943196948191677679072983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5962131298794451786048655 8943196948191677679072983)
    ·
      refine ⟨13414795422287516518609475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8943196948191677679072983 13414795422287516518609475)
      ·
        refine ⟨20122193133431274777914213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13414795422287516518609475 20122193133431274777914213)
        ·
          refine ⟨3772911212518364020858915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20122193133431274777914213 3772911212518364020858915)
          ·
            refine ⟨5659366818777546031288373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3772911212518364020858915 5659366818777546031288373)
            ·
              refine ⟨530565639260394940433285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5659366818777546031288373 530565639260394940433285)
              ·
                refine ⟨99481057361324051331241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 530565639260394940433285 99481057361324051331241)
                ·
                  refine ⟨74610793020993038498431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99481057361324051331241 74610793020993038498431)
                  ·
                    rfl

theorem cell20_163467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 4, 2].length) (baseStart_163467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163467 prefixEnd_163467 := by exact prefixLift 163467
  have htrace : WordTrace (prefixWord ++ tailWord_163467) baseStart_163467 baseEnd_163467 := by
    simpa [prefixWord, tailWord_163467, baseEnd_163467] using wordTrace_append hprefix tailTrace_163467
  have hstable : (prefixWord ++ tailWord_163467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163467).length < 2 ^ (prefixWord ++ tailWord_163467).sum := by decide
  have hdescent : baseEnd_163467 < baseStart_163467 := by decide
  rcases family_descends (prefixWord ++ tailWord_163467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163488 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_163488 : Nat := 118140960795 + 163488 * 2 ^ 59
def prefixEnd_163488 : Nat := 4983230072969 + 3 ^ 40 * 163488 * 2
def baseEnd_163488 : Nat := 74620377993210298798345

theorem tailTrace_163488 : CollatzResearch.WordTrace tailWord_163488 prefixEnd_163488 74620377993210298798345 := by
  unfold tailWord_163488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981448615859186186281559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3975264821145581581708745 2981448615859186186281559)
  ·
    refine ⟨4472172923788779279422339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2981448615859186186281559 4472172923788779279422339)
    ·
      refine ⟨6708259385683168919133509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4472172923788779279422339 6708259385683168919133509)
      ·
        refine ⟨1257798634815594172337533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6708259385683168919133509 1257798634815594172337533)
        ·
          refine ⟨471674488055847814626575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1257798634815594172337533 471674488055847814626575)
          ·
            refine ⟨707511732083771721939863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471674488055847814626575 707511732083771721939863)
            ·
              refine ⟨1061267598125657582909795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707511732083771721939863 1061267598125657582909795)
              ·
                refine ⟨1591901397188486374364693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1061267598125657582909795 1591901397188486374364693)
                ·
                  refine ⟨74620377993210298798345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1591901397188486374364693 74620377993210298798345)
                  ·
                    rfl

theorem cell20_163488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_163488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163488 prefixEnd_163488 := by exact prefixLift 163488
  have htrace : WordTrace (prefixWord ++ tailWord_163488) baseStart_163488 baseEnd_163488 := by
    simpa [prefixWord, tailWord_163488, baseEnd_163488] using wordTrace_append hprefix tailTrace_163488
  have hstable : (prefixWord ++ tailWord_163488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163488).length < 2 ^ (prefixWord ++ tailWord_163488).sum := by decide
  have hdescent : baseEnd_163488 < baseStart_163488 := by decide
  rcases family_descends (prefixWord ++ tailWord_163488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163542 : List Nat := [5, 2, 1, 3, 2, 1, 2, 4]
def baseStart_163542 : Nat := 118140960795 + 163542 * 2 ^ 59
def prefixEnd_163542 : Nat := 4983230072969 + 3 ^ 40 * 163542 * 2
def baseEnd_163542 : Nat := 24881675021542036999375

theorem tailTrace_163542 : CollatzResearch.WordTrace tailWord_163542 prefixEnd_163542 24881675021542036999375 := by
  unfold tailWord_163542
  simp only [CollatzResearch.WordTrace]
  refine ⟨372804173345171224689305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3976577849015159730019253 372804173345171224689305)
  ·
    refine ⟨279603130008878418516979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 372804173345171224689305 279603130008878418516979)
    ·
      refine ⟨419404695013317627775469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 279603130008878418516979 419404695013317627775469)
      ·
        refine ⟨157276760629994110415801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 419404695013317627775469 157276760629994110415801)
        ·
          refine ⟨117957570472495582811851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157276760629994110415801 117957570472495582811851)
          ·
            refine ⟨176936355708743374217777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117957570472495582811851 176936355708743374217777)
            ·
              refine ⟨132702266781557530663333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176936355708743374217777 132702266781557530663333)
              ·
                refine ⟨24881675021542036999375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132702266781557530663333 24881675021542036999375)
                ·
                  rfl

theorem cell20_163542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_163542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163542 prefixEnd_163542 := by exact prefixLift 163542
  have htrace : WordTrace (prefixWord ++ tailWord_163542) baseStart_163542 baseEnd_163542 := by
    simpa [prefixWord, tailWord_163542, baseEnd_163542] using wordTrace_append hprefix tailTrace_163542
  have hstable : (prefixWord ++ tailWord_163542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163542).length < 2 ^ (prefixWord ++ tailWord_163542).sum := by decide
  have hdescent : baseEnd_163542 < baseStart_163542 := by decide
  rcases family_descends (prefixWord ++ tailWord_163542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163560 : List Nat := [2, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_163560 : Nat := 118140960795 + 163560 * 2 ^ 59
def prefixEnd_163560 : Nat := 4983230072969 + 3 ^ 40 * 163560 * 2
def baseEnd_163560 : Nat := 74653240755098048398051

theorem tailTrace_163560 : CollatzResearch.WordTrace tailWord_163560 prefixEnd_163560 74653240755098048398051 := by
  unfold tailWord_163560
  simp only [CollatzResearch.WordTrace]
  refine ⟨2982761643728764334592067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3977015524971685779456089 2982761643728764334592067)
  ·
    refine ⟨4474142465593146501888101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2982761643728764334592067 4474142465593146501888101)
    ·
      refine ⟨838901712298714969104019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4474142465593146501888101 838901712298714969104019)
      ·
        refine ⟨1258352568448072453656029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 838901712298714969104019 1258352568448072453656029)
        ·
          refine ⟨471882213168027170121011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1258352568448072453656029 471882213168027170121011)
          ·
            refine ⟨707823319752040755181517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 471882213168027170121011 707823319752040755181517)
            ·
              refine ⟨265433744907015283193069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 707823319752040755181517 265433744907015283193069)
              ·
                refine ⟨99537654340130731197401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 265433744907015283193069 99537654340130731197401)
                ·
                  refine ⟨74653240755098048398051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99537654340130731197401 74653240755098048398051)
                  ·
                    rfl

theorem cell20_163560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_163560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163560 prefixEnd_163560 := by exact prefixLift 163560
  have htrace : WordTrace (prefixWord ++ tailWord_163560) baseStart_163560 baseEnd_163560 := by
    simpa [prefixWord, tailWord_163560, baseEnd_163560] using wordTrace_append hprefix tailTrace_163560
  have hstable : (prefixWord ++ tailWord_163560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163560).length < 2 ^ (prefixWord ++ tailWord_163560).sum := by decide
  have hdescent : baseEnd_163560 < baseStart_163560 := by decide
  rcases family_descends (prefixWord ++ tailWord_163560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163588 : List Nat := [2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_163588 : Nat := 118140960795 + 163588 * 2 ^ 59
def prefixEnd_163588 : Nat := 4983230072969 + 3 ^ 40 * 163588 * 2
def baseEnd_163588 : Nat := 24888673572684798488201

theorem tailTrace_163588 : CollatzResearch.WordTrace tailWord_163588 prefixEnd_163588 24888673572684798488201 := by
  unfold tailWord_163588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983272265678044725601709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3977696354237392967468945 2983272265678044725601709)
  ·
    refine ⟨1118727099629266772100641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2983272265678044725601709 1118727099629266772100641)
    ·
      refine ⟨839045324721950079075481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1118727099629266772100641 839045324721950079075481)
      ·
        refine ⟨629283993541462559306611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839045324721950079075481 629283993541462559306611)
        ·
          refine ⟨943925990312193838959917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629283993541462559306611 943925990312193838959917)
          ·
            refine ⟨353972246367072689609969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 943925990312193838959917 353972246367072689609969)
            ·
              refine ⟨265479184775304517207477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353972246367072689609969 265479184775304517207477)
              ·
                refine ⟨24888673572684798488201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 265479184775304517207477 24888673572684798488201)
                ·
                  rfl

theorem cell20_163588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_163588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163588 prefixEnd_163588 := by exact prefixLift 163588
  have htrace : WordTrace (prefixWord ++ tailWord_163588) baseStart_163588 baseEnd_163588 := by
    simpa [prefixWord, tailWord_163588, baseEnd_163588] using wordTrace_append hprefix tailTrace_163588
  have hstable : (prefixWord ++ tailWord_163588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163588).length < 2 ^ (prefixWord ++ tailWord_163588).sum := by decide
  have hdescent : baseEnd_163588 < baseStart_163588 := by decide
  rcases family_descends (prefixWord ++ tailWord_163588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163633 : List Nat := [1, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_163633 : Nat := 118140960795 + 163633 * 2 ^ 59
def prefixEnd_163633 : Nat := 4983230072969 + 3 ^ 40 * 163633 * 2
def baseEnd_163633 : Nat := 74686559944234238964419

theorem tailTrace_163633 : CollatzResearch.WordTrace tailWord_163633 prefixEnd_163633 74686559944234238964419 := by
  unfold tailWord_163633
  simp only [CollatzResearch.WordTrace]
  refine ⟨5968185816193062136591553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3978790544128708091061035 5968185816193062136591553)
  ·
    refine ⟨4476139362144796602443665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5968185816193062136591553 4476139362144796602443665)
    ·
      refine ⟨3357104521608597451832749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4476139362144796602443665 3357104521608597451832749)
      ·
        refine ⟨1258914195603224044437281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3357104521608597451832749 1258914195603224044437281)
        ·
          refine ⟨944185646702418033327961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1258914195603224044437281 944185646702418033327961)
          ·
            refine ⟨708139235026813524995971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 944185646702418033327961 708139235026813524995971)
            ·
              refine ⟨1062208852540220287493957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708139235026813524995971 1062208852540220287493957)
              ·
                refine ⟨199164159851291303905117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1062208852540220287493957 199164159851291303905117)
                ·
                  refine ⟨74686559944234238964419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199164159851291303905117 74686559944234238964419)
                  ·
                    rfl

theorem cell20_163633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_163633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163633 prefixEnd_163633 := by exact prefixLift 163633
  have htrace : WordTrace (prefixWord ++ tailWord_163633) baseStart_163633 baseEnd_163633 := by
    simpa [prefixWord, tailWord_163633, baseEnd_163633] using wordTrace_append hprefix tailTrace_163633
  have hstable : (prefixWord ++ tailWord_163633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163633).length < 2 ^ (prefixWord ++ tailWord_163633).sum := by decide
  have hdescent : baseEnd_163633 < baseStart_163633 := by decide
  rcases family_descends (prefixWord ++ tailWord_163633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163716 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_163716 : Nat := 118140960795 + 163716 * 2 ^ 59
def prefixEnd_163716 : Nat := 4983230072969 + 3 ^ 40 * 163716 * 2
def baseEnd_163716 : Nat := 74724443405854839197413

theorem tailTrace_163716 : CollatzResearch.WordTrace tailWord_163716 prefixEnd_163716 74724443405854839197413 := by
  unfold tailWord_163716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2985606537446183655931501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3980808716594911541242001 2985606537446183655931501)
  ·
    refine ⟨1119602451542318870974313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2985606537446183655931501 1119602451542318870974313)
    ·
      refine ⟨839701838656739153230735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119602451542318870974313 839701838656739153230735)
      ·
        refine ⟨1259552757985108729846103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839701838656739153230735 1259552757985108729846103)
        ·
          refine ⟨1889329136977663094769155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1259552757985108729846103 1889329136977663094769155)
          ·
            refine ⟨2833993705466494642153733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1889329136977663094769155 2833993705466494642153733)
            ·
              refine ⟨531373819774967745403825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2833993705466494642153733 531373819774967745403825)
              ·
                refine ⟨398530364831225809052869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 531373819774967745403825 398530364831225809052869)
                ·
                  refine ⟨74724443405854839197413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398530364831225809052869 74724443405854839197413)
                  ·
                    rfl

theorem cell20_163716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_163716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163716 prefixEnd_163716 := by exact prefixLift 163716
  have htrace : WordTrace (prefixWord ++ tailWord_163716) baseStart_163716 baseEnd_163716 := by
    simpa [prefixWord, tailWord_163716, baseEnd_163716] using wordTrace_append hprefix tailTrace_163716
  have hstable : (prefixWord ++ tailWord_163716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163716).length < 2 ^ (prefixWord ++ tailWord_163716).sum := by decide
  have hdescent : baseEnd_163716 < baseStart_163716 := by decide
  rcases family_descends (prefixWord ++ tailWord_163716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163719 : List Nat := [1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_163719 : Nat := 118140960795 + 163719 * 2 ^ 59
def prefixEnd_163719 : Nat := 4983230072969 + 3 ^ 40 * 163719 * 2
def baseEnd_163719 : Nat := 24908604229200054032467

theorem tailTrace_163719 : CollatzResearch.WordTrace tailWord_163719 prefixEnd_163719 24908604229200054032467 := by
  unfold tailWord_163719
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971322493881498824222211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3980881662587665882814807 5971322493881498824222211)
  ·
    refine ⟨8956983740822248236333317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5971322493881498824222211 8956983740822248236333317)
    ·
      refine ⟨1679434451404171544312497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8956983740822248236333317 1679434451404171544312497)
      ·
        refine ⟨1259575838553128658234373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1679434451404171544312497 1259575838553128658234373)
        ·
          refine ⟨236170469728711623418945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1259575838553128658234373 236170469728711623418945)
          ·
            refine ⟨177127852296533717564209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236170469728711623418945 177127852296533717564209)
            ·
              refine ⟨132845889222400288173157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177127852296533717564209 132845889222400288173157)
              ·
                refine ⟨24908604229200054032467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 132845889222400288173157 24908604229200054032467)
                ·
                  rfl

theorem cell20_163719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_163719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163719 prefixEnd_163719 := by exact prefixLift 163719
  have htrace : WordTrace (prefixWord ++ tailWord_163719) baseStart_163719 baseEnd_163719 := by
    simpa [prefixWord, tailWord_163719, baseEnd_163719] using wordTrace_append hprefix tailTrace_163719
  have hstable : (prefixWord ++ tailWord_163719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163719).length < 2 ^ (prefixWord ++ tailWord_163719).sum := by decide
  have hdescent : baseEnd_163719 < baseStart_163719 := by decide
  rcases family_descends (prefixWord ++ tailWord_163719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163737 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 6]
def baseStart_163737 : Nat := 118140960795 + 163737 * 2 ^ 59
def prefixEnd_163737 : Nat := 4983230072969 + 3 ^ 40 * 163737 * 2
def baseEnd_163737 : Nat := 74734028378072099497327

theorem tailTrace_163737 : CollatzResearch.WordTrace tailWord_163737 prefixEnd_163737 74734028378072099497327 := by
  unfold tailWord_163737
  simp only [CollatzResearch.WordTrace]
  refine ⟨5971979007816287898377465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3981319338544191932251643 5971979007816287898377465)
  ·
    refine ⟨4478984255862215923783099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5971979007816287898377465 4478984255862215923783099)
    ·
      refine ⟨6718476383793323885674649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4478984255862215923783099 6718476383793323885674649)
      ·
        refine ⟨5038857287844992914255987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6718476383793323885674649 5038857287844992914255987)
        ·
          refine ⟨7558285931767489371383981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5038857287844992914255987 7558285931767489371383981)
          ·
            refine ⟨2834357224412808514268993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7558285931767489371383981 2834357224412808514268993)
            ·
              refine ⟨2125767918309606385701745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2834357224412808514268993 2125767918309606385701745)
              ·
                refine ⟨1594325938732204789276309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2125767918309606385701745 1594325938732204789276309)
                ·
                  refine ⟨74734028378072099497327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1594325938732204789276309 74734028378072099497327)
                  ·
                    rfl

theorem cell20_163737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_163737 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163737 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163737 prefixEnd_163737 := by exact prefixLift 163737
  have htrace : WordTrace (prefixWord ++ tailWord_163737) baseStart_163737 baseEnd_163737 := by
    simpa [prefixWord, tailWord_163737, baseEnd_163737] using wordTrace_append hprefix tailTrace_163737
  have hstable : (prefixWord ++ tailWord_163737).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163737).length < 2 ^ (prefixWord ++ tailWord_163737).sum := by decide
  have hdescent : baseEnd_163737 < baseStart_163737 := by decide
  rcases family_descends (prefixWord ++ tailWord_163737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163740 : List Nat := [2, 2, 3, 3, 1, 3, 6]
def baseStart_163740 : Nat := 118140960795 + 163740 * 2 ^ 59
def prefixEnd_163740 : Nat := 4983230072969 + 3 ^ 40 * 163740 * 2
def baseEnd_163740 : Nat := 8303933073313046933035

theorem tailTrace_163740 : CollatzResearch.WordTrace tailWord_163740 prefixEnd_163740 8303933073313046933035 := by
  unfold tailWord_163740
  simp only [CollatzResearch.WordTrace]
  refine ⟨2986044213402709705368337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3981392284536946273824449 2986044213402709705368337)
  ·
    refine ⟨2239533160052032279026253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2986044213402709705368337 2239533160052032279026253)
    ·
      refine ⟨839824935019512104634845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2239533160052032279026253 839824935019512104634845)
      ·
        refine ⟨314934350632317039238067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 839824935019512104634845 314934350632317039238067)
        ·
          refine ⟨472401525948475558857101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 314934350632317039238067 472401525948475558857101)
          ·
            refine ⟨177150572230678334571413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 472401525948475558857101 177150572230678334571413)
            ·
              refine ⟨8303933073313046933035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177150572230678334571413 8303933073313046933035)
              ·
                rfl

theorem cell20_163740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 6].length) (baseStart_163740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163740 prefixEnd_163740 := by exact prefixLift 163740
  have htrace : WordTrace (prefixWord ++ tailWord_163740) baseStart_163740 baseEnd_163740 := by
    simpa [prefixWord, tailWord_163740, baseEnd_163740] using wordTrace_append hprefix tailTrace_163740
  have hstable : (prefixWord ++ tailWord_163740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163740).length < 2 ^ (prefixWord ++ tailWord_163740).sum := by decide
  have hdescent : baseEnd_163740 < baseStart_163740 := by decide
  rcases family_descends (prefixWord ++ tailWord_163740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163761 : List Nat := [1, 2, 2, 4, 2, 1, 1, 7]
def baseStart_163761 : Nat := 118140960795 + 163761 * 2 ^ 59
def prefixEnd_163761 : Nat := 4983230072969 + 3 ^ 40 * 163761 * 2
def baseEnd_163761 : Nat := 24914994210678227565743

theorem tailTrace_163761 : CollatzResearch.WordTrace tailWord_163761 prefixEnd_163761 24914994210678227565743 := by
  unfold tailWord_163761
  simp only [CollatzResearch.WordTrace]
  refine ⟨5972854359729339997251137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3981902906486226664834091 5972854359729339997251137)
  ·
    refine ⟨4479640769797004997938353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5972854359729339997251137 4479640769797004997938353)
    ·
      refine ⟨3359730577347753748453765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4479640769797004997938353 3359730577347753748453765)
      ·
        refine ⟨629949483252703827835081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3359730577347753748453765 629949483252703827835081)
        ·
          refine ⟨472462112439527870876311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 629949483252703827835081 472462112439527870876311)
          ·
            refine ⟨708693168659291806314467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472462112439527870876311 708693168659291806314467)
            ·
              refine ⟨1063039752988937709471701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 708693168659291806314467 1063039752988937709471701)
              ·
                refine ⟨24914994210678227565743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1063039752988937709471701 24914994210678227565743)
                ·
                  rfl

theorem cell20_163761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 7].length) (baseStart_163761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163761 prefixEnd_163761 := by exact prefixLift 163761
  have htrace : WordTrace (prefixWord ++ tailWord_163761) baseStart_163761 baseEnd_163761 := by
    simpa [prefixWord, tailWord_163761, baseEnd_163761] using wordTrace_append hprefix tailTrace_163761
  have hstable : (prefixWord ++ tailWord_163761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163761).length < 2 ^ (prefixWord ++ tailWord_163761).sum := by decide
  have hdescent : baseEnd_163761 < baseStart_163761 := by decide
  rcases family_descends (prefixWord ++ tailWord_163761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163775 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 6]
def baseStart_163775 : Nat := 118140960795 + 163775 * 2 ^ 59
def prefixEnd_163775 : Nat := 4983230072969 + 3 ^ 40 * 163775 * 2
def baseEnd_163775 : Nat := 74751372613512856230505

theorem tailTrace_163775 : CollatzResearch.WordTrace tailWord_163775 prefixEnd_163775 74751372613512856230505 := by
  unfold tailWord_163775
  simp only [CollatzResearch.WordTrace]
  refine ⟨5973364981678620388260779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3982243321119080258840519 5973364981678620388260779)
  ·
    refine ⟨8960047472517930582391169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5973364981678620388260779 8960047472517930582391169)
    ·
      refine ⟨6720035604388447936793377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8960047472517930582391169 6720035604388447936793377)
      ·
        refine ⟨5040026703291335952595033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6720035604388447936793377 5040026703291335952595033)
        ·
          refine ⟨3780020027468501964446275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5040026703291335952595033 3780020027468501964446275)
          ·
            refine ⟨5670030041202752946669413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3780020027468501964446275 5670030041202752946669413)
            ·
              refine ⟨1063130632725516177500515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5670030041202752946669413 1063130632725516177500515)
              ·
                refine ⟨1594695949088274266250773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1063130632725516177500515 1594695949088274266250773)
                ·
                  refine ⟨74751372613512856230505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1594695949088274266250773 74751372613512856230505)
                  ·
                    rfl

theorem cell20_163775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_163775 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163775 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163775 prefixEnd_163775 := by exact prefixLift 163775
  have htrace : WordTrace (prefixWord ++ tailWord_163775) baseStart_163775 baseEnd_163775 := by
    simpa [prefixWord, tailWord_163775, baseEnd_163775] using wordTrace_append hprefix tailTrace_163775
  have hstable : (prefixWord ++ tailWord_163775).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163775).length < 2 ^ (prefixWord ++ tailWord_163775).sum := by decide
  have hdescent : baseEnd_163775 < baseStart_163775 := by decide
  rcases family_descends (prefixWord ++ tailWord_163775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163802 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 3]
def baseStart_163802 : Nat := 118140960795 + 163802 * 2 ^ 59
def prefixEnd_163802 : Nat := 4983230072969 + 3 ^ 40 * 163802 * 2
def baseEnd_163802 : Nat := 74763696149220762330395

theorem tailTrace_163802 : CollatzResearch.WordTrace tailWord_163802 prefixEnd_163802 74763696149220762330395 := by
  unfold tailWord_163802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1493587438145200999873415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3982899835053869332995773 1493587438145200999873415)
  ·
    refine ⟨2240381157217801499810123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1493587438145200999873415 2240381157217801499810123)
    ·
      refine ⟨3360571735826702249715185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2240381157217801499810123 3360571735826702249715185)
      ·
        refine ⟨2520428801870026687286389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3360571735826702249715185 2520428801870026687286389)
        ·
          refine ⟨236290200175315001933099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2520428801870026687286389 236290200175315001933099)
          ·
            refine ⟨354435300262972502899649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236290200175315001933099 354435300262972502899649)
            ·
              refine ⟨265826475197229377174737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354435300262972502899649 265826475197229377174737)
              ·
                refine ⟨199369856397922032881053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265826475197229377174737 199369856397922032881053)
                ·
                  refine ⟨74763696149220762330395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199369856397922032881053 74763696149220762330395)
                  ·
                    rfl

theorem cell20_163802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_163802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163802 prefixEnd_163802 := by exact prefixLift 163802
  have htrace : WordTrace (prefixWord ++ tailWord_163802) baseStart_163802 baseEnd_163802 := by
    simpa [prefixWord, tailWord_163802, baseEnd_163802] using wordTrace_append hprefix tailTrace_163802
  have hstable : (prefixWord ++ tailWord_163802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163802).length < 2 ^ (prefixWord ++ tailWord_163802).sum := by decide
  have hdescent : baseEnd_163802 < baseStart_163802 := by decide
  rcases family_descends (prefixWord ++ tailWord_163802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163847 : List Nat := [1, 1, 4, 3, 1, 2, 1, 5, 2]
def baseStart_163847 : Nat := 118140960795 + 163847 * 2 ^ 59
def prefixEnd_163847 : Nat := 4983230072969 + 3 ^ 40 * 163847 * 2
def baseEnd_163847 : Nat := 74784235375400605830211

theorem tailTrace_163847 : CollatzResearch.WordTrace tailWord_163847 prefixEnd_163847 74784235375400605830211 := by
  unfold tailWord_163847
  simp only [CollatzResearch.WordTrace]
  refine ⟨5975991037417776684881795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3983994024945184456587863 5975991037417776684881795)
  ·
    refine ⟨8963986556126665027322693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5975991037417776684881795 8963986556126665027322693)
    ·
      refine ⟨1680747479273749692623005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8963986556126665027322693 1680747479273749692623005)
      ·
        refine ⟨630280304727656134733627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1680747479273749692623005 630280304727656134733627)
        ·
          refine ⟨945420457091484202100441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630280304727656134733627 945420457091484202100441)
          ·
            refine ⟨709065342818613151575331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 945420457091484202100441 709065342818613151575331)
            ·
              refine ⟨1063598014227919727362997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709065342818613151575331 1063598014227919727362997)
              ·
                refine ⟨99712313833867474440281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1063598014227919727362997 99712313833867474440281)
                ·
                  refine ⟨74784235375400605830211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99712313833867474440281 74784235375400605830211)
                  ·
                    rfl

theorem cell20_163847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 5, 2].length) (baseStart_163847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163847 prefixEnd_163847 := by exact prefixLift 163847
  have htrace : WordTrace (prefixWord ++ tailWord_163847) baseStart_163847 baseEnd_163847 := by
    simpa [prefixWord, tailWord_163847, baseEnd_163847] using wordTrace_append hprefix tailTrace_163847
  have hstable : (prefixWord ++ tailWord_163847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163847).length < 2 ^ (prefixWord ++ tailWord_163847).sum := by decide
  have hdescent : baseEnd_163847 < baseStart_163847 := by decide
  rcases family_descends (prefixWord ++ tailWord_163847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163851 : List Nat := [1, 1, 1, 1, 6, 1, 1, 2, 6]
def baseStart_163851 : Nat := 118140960795 + 163851 * 2 ^ 59
def prefixEnd_163851 : Nat := 4983230072969 + 3 ^ 40 * 163851 * 2
def baseEnd_163851 : Nat := 74786061084394369696861

theorem tailTrace_163851 : CollatzResearch.WordTrace tailWord_163851 prefixEnd_163851 74786061084394369696861 := by
  unfold tailWord_163851
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976136929403285368027407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3984091286268856912018271 5976136929403285368027407)
  ·
    refine ⟨8964205394104928052041111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5976136929403285368027407 8964205394104928052041111)
    ·
      refine ⟨13446308091157392078061667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8964205394104928052041111 13446308091157392078061667)
      ·
        refine ⟨20169462136736088117092501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13446308091157392078061667 20169462136736088117092501)
        ·
          refine ⟨945443537659504130488711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20169462136736088117092501 945443537659504130488711)
          ·
            refine ⟨1418165306489256195733067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945443537659504130488711 1418165306489256195733067)
            ·
              refine ⟨2127247959733884293599601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1418165306489256195733067 2127247959733884293599601)
              ·
                refine ⟨1595435969800413220199701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2127247959733884293599601 1595435969800413220199701)
                ·
                  refine ⟨74786061084394369696861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1595435969800413220199701 74786061084394369696861)
                  ·
                    rfl

theorem cell20_163851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 6].length) (baseStart_163851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163851 prefixEnd_163851 := by exact prefixLift 163851
  have htrace : WordTrace (prefixWord ++ tailWord_163851) baseStart_163851 baseEnd_163851 := by
    simpa [prefixWord, tailWord_163851, baseEnd_163851] using wordTrace_append hprefix tailTrace_163851
  have hstable : (prefixWord ++ tailWord_163851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163851).length < 2 ^ (prefixWord ++ tailWord_163851).sum := by decide
  have hdescent : baseEnd_163851 < baseStart_163851 := by decide
  rcases family_descends (prefixWord ++ tailWord_163851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163853 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 3]
def baseStart_163853 : Nat := 118140960795 + 163853 * 2 ^ 59
def prefixEnd_163853 : Nat := 4983230072969 + 3 ^ 40 * 163853 * 2
def baseEnd_163853 : Nat := 74786973938891251630187

theorem tailTrace_163853 : CollatzResearch.WordTrace tailWord_163853 prefixEnd_163853 74786973938891251630187 := by
  unfold tailWord_163853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976209875396039709600213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3984139916930693139733475 5976209875396039709600213)
  ·
    refine ⟨140067418954594680693755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 5976209875396039709600213 140067418954594680693755)
    ·
      refine ⟨210101128431892021040633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140067418954594680693755 210101128431892021040633)
      ·
        refine ⟨157575846323919015780475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210101128431892021040633 157575846323919015780475)
        ·
          refine ⟨236363769485878523670713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157575846323919015780475 236363769485878523670713)
          ·
            refine ⟨177272827114408892753035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 236363769485878523670713 177272827114408892753035)
            ·
              refine ⟨265909240671613339129553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177272827114408892753035 265909240671613339129553)
              ·
                refine ⟨199431930503710004347165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265909240671613339129553 199431930503710004347165)
                ·
                  refine ⟨74786973938891251630187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199431930503710004347165 74786973938891251630187)
                  ·
                    rfl

theorem cell20_163853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_163853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163853 prefixEnd_163853 := by exact prefixLift 163853
  have htrace : WordTrace (prefixWord ++ tailWord_163853) baseStart_163853 baseEnd_163853 := by
    simpa [prefixWord, tailWord_163853, baseEnd_163853] using wordTrace_append hprefix tailTrace_163853
  have hstable : (prefixWord ++ tailWord_163853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163853).length < 2 ^ (prefixWord ++ tailWord_163853).sum := by decide
  have hdescent : baseEnd_163853 < baseStart_163853 := by decide
  rcases family_descends (prefixWord ++ tailWord_163853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163861 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_163861 : Nat := 118140960795 + 163861 * 2 ^ 59
def prefixEnd_163861 : Nat := 4983230072969 + 3 ^ 40 * 163861 * 2
def baseEnd_163861 : Nat := 74790625356878779363487

theorem tailTrace_163861 : CollatzResearch.WordTrace tailWord_163861 prefixEnd_163861 74790625356878779363487 := by
  unfold tailWord_163861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5976501659367057075891437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3984334439578038050594291 5976501659367057075891437)
  ·
    refine ⟨2241188122262646403459289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5976501659367057075891437 2241188122262646403459289)
    ·
      refine ⟨1680891091696984802594467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2241188122262646403459289 1680891091696984802594467)
      ·
        refine ⟨2521336637545477203891701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1680891091696984802594467 2521336637545477203891701)
        ·
          refine ⟨236375309769888487864847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2521336637545477203891701 236375309769888487864847)
          ·
            refine ⟨354562964654832731797271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236375309769888487864847 354562964654832731797271)
            ·
              refine ⟨531844446982249097695907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 354562964654832731797271 531844446982249097695907)
              ·
                refine ⟨797766670473373646543861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 531844446982249097695907 797766670473373646543861)
                ·
                  refine ⟨74790625356878779363487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 797766670473373646543861 74790625356878779363487)
                  ·
                    rfl

theorem cell20_163861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_163861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163861 prefixEnd_163861 := by exact prefixLift 163861
  have htrace : WordTrace (prefixWord ++ tailWord_163861) baseStart_163861 baseEnd_163861 := by
    simpa [prefixWord, tailWord_163861, baseEnd_163861] using wordTrace_append hprefix tailTrace_163861
  have hstable : (prefixWord ++ tailWord_163861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163861).length < 2 ^ (prefixWord ++ tailWord_163861).sum := by decide
  have hdescent : baseEnd_163861 < baseStart_163861 := by decide
  rcases family_descends (prefixWord ++ tailWord_163861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163868 : List Nat := [2, 2, 3, 1, 3, 1, 1, 3, 4]
def baseStart_163868 : Nat := 118140960795 + 163868 * 2 ^ 59
def prefixEnd_163868 : Nat := 4983230072969 + 3 ^ 40 * 163868 * 2
def baseEnd_163868 : Nat := 74793820347617866130125

theorem tailTrace_163868 : CollatzResearch.WordTrace tailWord_163868 prefixEnd_163868 74793820347617866130125 := by
  unfold tailWord_163868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2988378485170848635698129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3984504646894464847597505 2988378485170848635698129)
  ·
    refine ⟨2241283863878136476773597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2988378485170848635698129 2241283863878136476773597)
    ·
      refine ⟨840481448954301178790099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2241283863878136476773597 840481448954301178790099)
      ·
        refine ⟨1260722173431451768185149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 840481448954301178790099 1260722173431451768185149)
        ·
          refine ⟨472770815036794413069431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1260722173431451768185149 472770815036794413069431)
          ·
            refine ⟨709156222555191619604147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472770815036794413069431 709156222555191619604147)
            ·
              refine ⟨1063734333832787429406221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 709156222555191619604147 1063734333832787429406221)
              ·
                refine ⟨398900375187295286027333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1063734333832787429406221 398900375187295286027333)
                ·
                  refine ⟨74793820347617866130125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 398900375187295286027333 74793820347617866130125)
                  ·
                    rfl

theorem cell20_163868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_163868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163868 prefixEnd_163868 := by exact prefixLift 163868
  have htrace : WordTrace (prefixWord ++ tailWord_163868) baseStart_163868 baseEnd_163868 := by
    simpa [prefixWord, tailWord_163868, baseEnd_163868] using wordTrace_append hprefix tailTrace_163868
  have hstable : (prefixWord ++ tailWord_163868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163868).length < 2 ^ (prefixWord ++ tailWord_163868).sum := by decide
  have hdescent : baseEnd_163868 < baseStart_163868 := by decide
  rcases family_descends (prefixWord ++ tailWord_163868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163933 : List Nat := [1, 4, 4, 1, 1, 1, 4, 1, 3]
def baseStart_163933 : Nat := 118140960795 + 163933 * 2 ^ 59
def prefixEnd_163933 : Nat := 4983230072969 + 3 ^ 40 * 163933 * 2
def baseEnd_163933 : Nat := 74823488118766528963193

theorem tailTrace_163933 : CollatzResearch.WordTrace tailWord_163933 prefixEnd_163933 74823488118766528963193 := by
  unfold tailWord_163933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5979127715106213372512453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3986085143404142248341635 5979127715106213372512453)
  ·
    refine ⟨1121086446582415007346085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5979127715106213372512453 1121086446582415007346085)
    ·
      refine ⟨210203708734202813877391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1121086446582415007346085 210203708734202813877391)
      ·
        refine ⟨315305563101304220816087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210203708734202813877391 315305563101304220816087)
        ·
          refine ⟨472958344651956331224131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315305563101304220816087 472958344651956331224131)
          ·
            refine ⟨709437516977934496836197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 472958344651956331224131 709437516977934496836197)
            ·
              refine ⟨133019534433362718156787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 709437516977934496836197 133019534433362718156787)
              ·
                refine ⟨199529301650044077235181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133019534433362718156787 199529301650044077235181)
                ·
                  refine ⟨74823488118766528963193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199529301650044077235181 74823488118766528963193)
                  ·
                    rfl

theorem cell20_163933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_163933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163933 prefixEnd_163933 := by exact prefixLift 163933
  have htrace : WordTrace (prefixWord ++ tailWord_163933) baseStart_163933 baseEnd_163933 := by
    simpa [prefixWord, tailWord_163933, baseEnd_163933] using wordTrace_append hprefix tailTrace_163933
  have hstable : (prefixWord ++ tailWord_163933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163933).length < 2 ^ (prefixWord ++ tailWord_163933).sum := by decide
  have hdescent : baseEnd_163933 < baseStart_163933 := by decide
  rcases family_descends (prefixWord ++ tailWord_163933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_163978 : List Nat := [3, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_163978 : Nat := 118140960795 + 163978 * 2 ^ 59
def prefixEnd_163978 : Nat := 4983230072969 + 3 ^ 40 * 163978 * 2
def baseEnd_163978 : Nat := 74844027344946372463009

theorem tailTrace_163978 : CollatzResearch.WordTrace tailWord_163978 prefixEnd_163978 74844027344946372463009 := by
  unfold tailWord_163978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495192249985796514475147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3987179333295457371933725 1495192249985796514475147)
  ·
    refine ⟨2242788374978694771712721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1495192249985796514475147 2242788374978694771712721)
    ·
      refine ⟨1682091281234021078784541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2242788374978694771712721 1682091281234021078784541)
      ·
        refine ⟨630784230462757904544203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1682091281234021078784541 630784230462757904544203)
        ·
          refine ⟨946176345694136856816305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630784230462757904544203 946176345694136856816305)
          ·
            refine ⟨709632259270602642612229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946176345694136856816305 709632259270602642612229)
            ·
              refine ⟨133056048613237995489793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 709632259270602642612229 133056048613237995489793)
              ·
                refine ⟨99792036459928496617345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133056048613237995489793 99792036459928496617345)
                ·
                  refine ⟨74844027344946372463009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99792036459928496617345 74844027344946372463009)
                  ·
                    rfl

theorem cell20_163978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_163978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_163978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_163978 prefixEnd_163978 := by exact prefixLift 163978
  have htrace : WordTrace (prefixWord ++ tailWord_163978) baseStart_163978 baseEnd_163978 := by
    simpa [prefixWord, tailWord_163978, baseEnd_163978] using wordTrace_append hprefix tailTrace_163978
  have hstable : (prefixWord ++ tailWord_163978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_163978).length < 2 ^ (prefixWord ++ tailWord_163978).sum := by decide
  have hdescent : baseEnd_163978 < baseStart_163978 := by decide
  rcases family_descends (prefixWord ++ tailWord_163978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164061 : List Nat := [1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_164061 : Nat := 118140960795 + 164061 * 2 ^ 59
def prefixEnd_164061 : Nat := 4983230072969 + 3 ^ 40 * 164061 * 2
def baseEnd_164061 : Nat := 24960636935522324232001

theorem tailTrace_164061 : CollatzResearch.WordTrace tailWord_164061 prefixEnd_164061 24960636935522324232001 := by
  unfold tailWord_164061
  simp only [CollatzResearch.WordTrace]
  refine ⟨5983796258642491233172037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3989197505761660822114691 5983796258642491233172037)
  ·
    refine ⟨1121961798495467106219757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5983796258642491233172037 1121961798495467106219757)
    ·
      refine ⟨420735674435800164832409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1121961798495467106219757 420735674435800164832409)
      ·
        refine ⟨315551755826850123624307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 420735674435800164832409 315551755826850123624307)
        ·
          refine ⟨473327633740275185436461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315551755826850123624307 473327633740275185436461)
          ·
            refine ⟨177497862652603194538673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 473327633740275185436461 177497862652603194538673)
            ·
              refine ⟨133123396989452395904005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 177497862652603194538673 133123396989452395904005)
              ·
                refine ⟨24960636935522324232001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133123396989452395904005 24960636935522324232001)
                ·
                  rfl

theorem cell20_164061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_164061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164061 prefixEnd_164061 := by exact prefixLift 164061
  have htrace : WordTrace (prefixWord ++ tailWord_164061) baseStart_164061 baseEnd_164061 := by
    simpa [prefixWord, tailWord_164061, baseEnd_164061] using wordTrace_append hprefix tailTrace_164061
  have hstable : (prefixWord ++ tailWord_164061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164061).length < 2 ^ (prefixWord ++ tailWord_164061).sum := by decide
  have hdescent : baseEnd_164061 < baseStart_164061 := by decide
  rcases family_descends (prefixWord ++ tailWord_164061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164072 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 5]
def baseStart_164072 : Nat := 118140960795 + 164072 * 2 ^ 59
def prefixEnd_164072 : Nat := 4983230072969 + 3 ^ 40 * 164072 * 2
def baseEnd_164072 : Nat := 74886931506299823329291

theorem tailTrace_164072 : CollatzResearch.WordTrace tailWord_164072 prefixEnd_164072 74886931506299823329291 := by
  unfold tailWord_164072
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992098730801320055911235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3989464974401760074548313 2992098730801320055911235)
  ·
    refine ⟨4488148096201980083866853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2992098730801320055911235 4488148096201980083866853)
    ·
      refine ⟨841527768037871265725035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4488148096201980083866853 841527768037871265725035)
      ·
        refine ⟨1262291652056806898587553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841527768037871265725035 1262291652056806898587553)
        ·
          refine ⟨946718739042605173940665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1262291652056806898587553 946718739042605173940665)
          ·
            refine ⟨710039054281953880455499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 946718739042605173940665 710039054281953880455499)
            ·
              refine ⟨1065058581422930820683249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 710039054281953880455499 1065058581422930820683249)
              ·
                refine ⟨798793936067198115512437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1065058581422930820683249 798793936067198115512437)
                ·
                  refine ⟨74886931506299823329291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 798793936067198115512437 74886931506299823329291)
                  ·
                    rfl

theorem cell20_164072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_164072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164072 prefixEnd_164072 := by exact prefixLift 164072
  have htrace : WordTrace (prefixWord ++ tailWord_164072) baseStart_164072 baseEnd_164072 := by
    simpa [prefixWord, tailWord_164072, baseEnd_164072] using wordTrace_append hprefix tailTrace_164072
  have hstable : (prefixWord ++ tailWord_164072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164072).length < 2 ^ (prefixWord ++ tailWord_164072).sum := by decide
  have hdescent : baseEnd_164072 < baseStart_164072 := by decide
  rcases family_descends (prefixWord ++ tailWord_164072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164092 : List Nat := [2, 2, 2, 1, 4, 2, 3, 2, 2]
def baseStart_164092 : Nat := 118140960795 + 164092 * 2 ^ 59
def prefixEnd_164092 : Nat := 4983230072969 + 3 ^ 40 * 164092 * 2
def baseEnd_164092 : Nat := 74896060051268642662543

theorem tailTrace_164092 : CollatzResearch.WordTrace tailWord_164092 prefixEnd_164092 74896060051268642662543 := by
  unfold tailWord_164092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992463460765091763775265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3989951281020122351700353 2992463460765091763775265)
  ·
    refine ⟨2244347595573818822831449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2992463460765091763775265 2244347595573818822831449)
    ·
      refine ⟨1683260696680364117123587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2244347595573818822831449 1683260696680364117123587)
      ·
        refine ⟨2524891045020546175685381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683260696680364117123587 2524891045020546175685381)
        ·
          refine ⟨473417070941352407941009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2524891045020546175685381 473417070941352407941009)
          ·
            refine ⟨355062803206014305955757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473417070941352407941009 355062803206014305955757)
            ·
              refine ⟨133148551202255364733409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355062803206014305955757 133148551202255364733409)
              ·
                refine ⟨99861413401691523550057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133148551202255364733409 99861413401691523550057)
                ·
                  refine ⟨74896060051268642662543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99861413401691523550057 74896060051268642662543)
                  ·
                    rfl

theorem cell20_164092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_164092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164092 prefixEnd_164092 := by exact prefixLift 164092
  have htrace : WordTrace (prefixWord ++ tailWord_164092) baseStart_164092 baseEnd_164092 := by
    simpa [prefixWord, tailWord_164092, baseEnd_164092] using wordTrace_append hprefix tailTrace_164092
  have hstable : (prefixWord ++ tailWord_164092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164092).length < 2 ^ (prefixWord ++ tailWord_164092).sum := by decide
  have hdescent : baseEnd_164092 < baseStart_164092 := by decide
  rcases family_descends (prefixWord ++ tailWord_164092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164096 : List Nat := [2, 1, 1, 2, 1, 1, 4, 6, 2]
def baseStart_164096 : Nat := 118140960795 + 164096 * 2 ^ 59
def prefixEnd_164096 : Nat := 4983230072969 + 3 ^ 40 * 164096 * 2
def baseEnd_164096 : Nat := 74897885760262406529193

theorem tailTrace_164096 : CollatzResearch.WordTrace tailWord_164096 prefixEnd_164096 74897885760262406529193 := by
  unfold tailWord_164096
  simp only [CollatzResearch.WordTrace]
  refine ⟨2992536406757846105348071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3990048542343794807130761 2992536406757846105348071)
  ·
    refine ⟨4488804610136769158022107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2992536406757846105348071 4488804610136769158022107)
    ·
      refine ⟨6733206915205153737033161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4488804610136769158022107 6733206915205153737033161)
      ·
        refine ⟨5049905186403865302774871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6733206915205153737033161 5049905186403865302774871)
        ·
          refine ⟨7574857779605797954162307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5049905186403865302774871 7574857779605797954162307)
          ·
            refine ⟨11362286669408696931243461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7574857779605797954162307 11362286669408696931243461)
            ·
              refine ⟨2130428750514130674608149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11362286669408696931243461 2130428750514130674608149)
              ·
                refine ⟨99863847680349875372257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2130428750514130674608149 99863847680349875372257)
                ·
                  refine ⟨74897885760262406529193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99863847680349875372257 74897885760262406529193)
                  ·
                    rfl

theorem cell20_164096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 6, 2].length) (baseStart_164096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164096 prefixEnd_164096 := by exact prefixLift 164096
  have htrace : WordTrace (prefixWord ++ tailWord_164096) baseStart_164096 baseEnd_164096 := by
    simpa [prefixWord, tailWord_164096, baseEnd_164096] using wordTrace_append hprefix tailTrace_164096
  have hstable : (prefixWord ++ tailWord_164096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164096).length < 2 ^ (prefixWord ++ tailWord_164096).sum := by decide
  have hdescent : baseEnd_164096 < baseStart_164096 := by decide
  rcases family_descends (prefixWord ++ tailWord_164096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164117 : List Nat := [1, 3, 2, 1, 2, 1, 2, 4, 4]
def baseStart_164117 : Nat := 118140960795 + 164117 * 2 ^ 59
def prefixEnd_164117 : Nat := 4983230072969 + 3 ^ 40 * 164117 * 2
def baseEnd_164117 : Nat := 74907470732479666829107

theorem tailTrace_164117 : CollatzResearch.WordTrace tailWord_164117 prefixEnd_164117 74907470732479666829107 := by
  unfold tailWord_164117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5985838746439612797210605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3990559164293075198140403 5985838746439612797210605)
  ·
    refine ⟨2244689529914854798953977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5985838746439612797210605 2244689529914854798953977)
    ·
      refine ⟨1683517147436141099215483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2244689529914854798953977 1683517147436141099215483)
      ·
        refine ⟨2525275721154211648823225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1683517147436141099215483 2525275721154211648823225)
        ·
          refine ⟨1893956790865658736617419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2525275721154211648823225 1893956790865658736617419)
          ·
            refine ⟨2840935186298488104926129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1893956790865658736617419 2840935186298488104926129)
            ·
              refine ⟨2130701389723866078694597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2840935186298488104926129 2130701389723866078694597)
              ·
                refine ⟨399506510573224889755237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2130701389723866078694597 399506510573224889755237)
                ·
                  refine ⟨74907470732479666829107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399506510573224889755237 74907470732479666829107)
                  ·
                    rfl

theorem cell20_164117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_164117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164117 prefixEnd_164117 := by exact prefixLift 164117
  have htrace : WordTrace (prefixWord ++ tailWord_164117) baseStart_164117 baseEnd_164117 := by
    simpa [prefixWord, tailWord_164117, baseEnd_164117] using wordTrace_append hprefix tailTrace_164117
  have hstable : (prefixWord ++ tailWord_164117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164117).length < 2 ^ (prefixWord ++ tailWord_164117).sum := by decide
  have hdescent : baseEnd_164117 < baseStart_164117 := by decide
  rcases family_descends (prefixWord ++ tailWord_164117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164141 : List Nat := [1, 5, 3, 1, 10]
def baseStart_164141 : Nat := 118140960795 + 164141 * 2 ^ 59
def prefixEnd_164141 : Nat := 4983230072969 + 3 ^ 40 * 164141 * 2
def baseEnd_164141 : Nat := 924918826993114197889

theorem tailTrace_164141 : CollatzResearch.WordTrace tailWord_164141 prefixEnd_164141 924918826993114197889 := by
  unfold tailWord_164141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5986714098352664896084277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3991142732235109930722851 5986714098352664896084277)
  ·
    refine ⟨561254446720562334007901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5986714098352664896084277 561254446720562334007901)
    ·
      refine ⟨210470417520210875252963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 561254446720562334007901 210470417520210875252963)
      ·
        refine ⟨315705626280316312879445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210470417520210875252963 315705626280316312879445)
        ·
          refine ⟨924918826993114197889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 315705626280316312879445 924918826993114197889)
          ·
            rfl

theorem cell20_164141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 10].length) (baseStart_164141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164141 prefixEnd_164141 := by exact prefixLift 164141
  have htrace : WordTrace (prefixWord ++ tailWord_164141) baseStart_164141 baseEnd_164141 := by
    simpa [prefixWord, tailWord_164141, baseEnd_164141] using wordTrace_append hprefix tailTrace_164141
  have hstable : (prefixWord ++ tailWord_164141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164141).length < 2 ^ (prefixWord ++ tailWord_164141).sum := by decide
  have hdescent : baseEnd_164141 < baseStart_164141 := by decide
  rcases family_descends (prefixWord ++ tailWord_164141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164158 : List Nat := [4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_164158 : Nat := 118140960795 + 164158 * 2 ^ 59
def prefixEnd_164158 : Nat := 4983230072969 + 3 ^ 40 * 164158 * 2
def baseEnd_164158 : Nat := 24975394749888582154091

theorem tailTrace_164158 : CollatzResearch.WordTrace tailWord_164158 prefixEnd_164158 24975394749888582154091 := by
  unfold tailWord_164158
  simp only [CollatzResearch.WordTrace]
  refine ⟨748416767411384599931641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3991556092860717866302085 748416767411384599931641)
  ·
    refine ⟨561312575558538449948731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 748416767411384599931641 561312575558538449948731)
    ·
      refine ⟨841968863337807674923097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 561312575558538449948731 841968863337807674923097)
      ·
        refine ⟨631476647503355756192323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 841968863337807674923097 631476647503355756192323)
        ·
          refine ⟨947214971255033634288485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 631476647503355756192323 947214971255033634288485)
          ·
            refine ⟨177602807110318806429091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 947214971255033634288485 177602807110318806429091)
            ·
              refine ⟨266404210665478209643637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177602807110318806429091 266404210665478209643637)
              ·
                refine ⟨24975394749888582154091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266404210665478209643637 24975394749888582154091)
                ·
                  rfl

theorem cell20_164158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_164158 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164158 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164158 prefixEnd_164158 := by exact prefixLift 164158
  have htrace : WordTrace (prefixWord ++ tailWord_164158) baseStart_164158 baseEnd_164158 := by
    simpa [prefixWord, tailWord_164158, baseEnd_164158] using wordTrace_append hprefix tailTrace_164158
  have hstable : (prefixWord ++ tailWord_164158).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164158).length < 2 ^ (prefixWord ++ tailWord_164158).sum := by decide
  have hdescent : baseEnd_164158 < baseStart_164158 := by decide
  rcases family_descends (prefixWord ++ tailWord_164158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164169 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 7]
def baseStart_164169 : Nat := 118140960795 + 164169 * 2 ^ 59
def prefixEnd_164169 : Nat := 4983230072969 + 3 ^ 40 * 164169 * 2
def baseEnd_164169 : Nat := 74931204949398597095561

theorem tailTrace_164169 : CollatzResearch.WordTrace tailWord_164169 prefixEnd_164169 74931204949398597095561 := by
  unfold tailWord_164169
  simp only [CollatzResearch.WordTrace]
  refine ⟨5987735342251225678103561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3991823561500817118735707 5987735342251225678103561)
  ·
    refine ⟨4490801506688419258577671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5987735342251225678103561 4490801506688419258577671)
    ·
      refine ⟨6736202260032628887866507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4490801506688419258577671 6736202260032628887866507)
      ·
        refine ⟨10104303390048943331799761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6736202260032628887866507 10104303390048943331799761)
        ·
          refine ⟨7578227542536707498849821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10104303390048943331799761 7578227542536707498849821)
          ·
            refine ⟨2841835328451265312068683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7578227542536707498849821 2841835328451265312068683)
            ·
              refine ⟨4262752992676897968103025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2841835328451265312068683 4262752992676897968103025)
              ·
                refine ⟨3197064744507673476077269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262752992676897968103025 3197064744507673476077269)
                ·
                  refine ⟨74931204949398597095561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3197064744507673476077269 74931204949398597095561)
                  ·
                    rfl

theorem cell20_164169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 7].length) (baseStart_164169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164169 prefixEnd_164169 := by exact prefixLift 164169
  have htrace : WordTrace (prefixWord ++ tailWord_164169) baseStart_164169 baseEnd_164169 := by
    simpa [prefixWord, tailWord_164169, baseEnd_164169] using wordTrace_append hprefix tailTrace_164169
  have hstable : (prefixWord ++ tailWord_164169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164169).length < 2 ^ (prefixWord ++ tailWord_164169).sum := by decide
  have hdescent : baseEnd_164169 < baseStart_164169 := by decide
  rcases family_descends (prefixWord ++ tailWord_164169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164210 : List Nat := [3, 2, 1, 2, 1, 4, 2, 1, 4]
def baseStart_164210 : Nat := 118140960795 + 164210 * 2 ^ 59
def prefixEnd_164210 : Nat := 4983230072969 + 3 ^ 40 * 164210 * 2
def baseEnd_164210 : Nat := 74949918466584676728727

theorem tailTrace_164210 : CollatzResearch.WordTrace tailWord_164210 prefixEnd_164210 74949918466584676728727 := by
  unfold tailWord_164210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497307683775672420086521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3992820490068459786897389 1497307683775672420086521)
  ·
    refine ⟨1122980762831754315064891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1497307683775672420086521 1122980762831754315064891)
    ·
      refine ⟨1684471144247631472597337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1122980762831754315064891 1684471144247631472597337)
      ·
        refine ⟨1263353358185723604448003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684471144247631472597337 1263353358185723604448003)
        ·
          refine ⟨1895030037278585406672005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263353358185723604448003 1895030037278585406672005)
          ·
            refine ⟨355318131989734763751001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1895030037278585406672005 355318131989734763751001)
            ·
              refine ⟨266488598992301072813251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355318131989734763751001 266488598992301072813251)
              ·
                refine ⟨399732898488451609219877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266488598992301072813251 399732898488451609219877)
                ·
                  refine ⟨74949918466584676728727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399732898488451609219877 74949918466584676728727)
                  ·
                    rfl

theorem cell20_164210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_164210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164210 prefixEnd_164210 := by exact prefixLift 164210
  have htrace : WordTrace (prefixWord ++ tailWord_164210) baseStart_164210 baseEnd_164210 := by
    simpa [prefixWord, tailWord_164210, baseEnd_164210] using wordTrace_append hprefix tailTrace_164210
  have hstable : (prefixWord ++ tailWord_164210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164210).length < 2 ^ (prefixWord ++ tailWord_164210).sum := by decide
  have hdescent : baseEnd_164210 < baseStart_164210 := by decide
  rcases family_descends (prefixWord ++ tailWord_164210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164231 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 4]
def baseStart_164231 : Nat := 118140960795 + 164231 * 2 ^ 59
def prefixEnd_164231 : Nat := 4983230072969 + 3 ^ 40 * 164231 * 2
def baseEnd_164231 : Nat := 74959503438801937028641

theorem tailTrace_164231 : CollatzResearch.WordTrace tailWord_164231 prefixEnd_164231 74959503438801937028641 := by
  unfold tailWord_164231
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989996668026610266860547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3993331112017740177907031 5989996668026610266860547)
  ·
    refine ⟨8984995002039915400290821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5989996668026610266860547 8984995002039915400290821)
    ·
      refine ⟨1684686562882484137554529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8984995002039915400290821 1684686562882484137554529)
      ·
        refine ⟨1263514922161863103165897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684686562882484137554529 1263514922161863103165897)
        ·
          refine ⟨947636191621397327374423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1263514922161863103165897 947636191621397327374423)
          ·
            refine ⟨1421454287432095991061635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947636191621397327374423 1421454287432095991061635)
            ·
              refine ⟨2132181431148143986592453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421454287432095991061635 2132181431148143986592453)
              ·
                refine ⟨399784018340276997486085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2132181431148143986592453 399784018340276997486085)
                ·
                  refine ⟨74959503438801937028641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 399784018340276997486085 74959503438801937028641)
                  ·
                    rfl

theorem cell20_164231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_164231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164231 prefixEnd_164231 := by exact prefixLift 164231
  have htrace : WordTrace (prefixWord ++ tailWord_164231) baseStart_164231 baseEnd_164231 := by
    simpa [prefixWord, tailWord_164231, baseEnd_164231] using wordTrace_append hprefix tailTrace_164231
  have hstable : (prefixWord ++ tailWord_164231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164231).length < 2 ^ (prefixWord ++ tailWord_164231).sum := by decide
  have hdescent : baseEnd_164231 < baseStart_164231 := by decide
  rcases family_descends (prefixWord ++ tailWord_164231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164234 : List Nat := [3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_164234 : Nat := 118140960795 + 164234 * 2 ^ 59
def prefixEnd_164234 : Nat := 4983230072969 + 3 ^ 40 * 164234 * 2
def baseEnd_164234 : Nat := 24986957573515753309543

theorem tailTrace_164234 : CollatzResearch.WordTrace tailWord_164234 prefixEnd_164234 24986957573515753309543 := by
  unfold tailWord_164234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497526521753935444804939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3993404058010494519479837 1497526521753935444804939)
  ·
    refine ⟨2246289782630903167207409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497526521753935444804939 2246289782630903167207409)
    ·
      refine ⟨1684717336973177375405557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2246289782630903167207409 1684717336973177375405557)
      ·
        refine ⟨157942250341235378944271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1684717336973177375405557 157942250341235378944271)
        ·
          refine ⟨236913375511853068416407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157942250341235378944271 236913375511853068416407)
          ·
            refine ⟨355370063267779602624611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236913375511853068416407 355370063267779602624611)
            ·
              refine ⟨533055094901669403936917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355370063267779602624611 533055094901669403936917)
              ·
                refine ⟨24986957573515753309543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 533055094901669403936917 24986957573515753309543)
                ·
                  rfl

theorem cell20_164234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_164234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164234 prefixEnd_164234 := by exact prefixLift 164234
  have htrace : WordTrace (prefixWord ++ tailWord_164234) baseStart_164234 baseEnd_164234 := by
    simpa [prefixWord, tailWord_164234, baseEnd_164234] using wordTrace_append hprefix tailTrace_164234
  have hstable : (prefixWord ++ tailWord_164234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164234).length < 2 ^ (prefixWord ++ tailWord_164234).sum := by decide
  have hdescent : baseEnd_164234 < baseStart_164234 := by decide
  rcases family_descends (prefixWord ++ tailWord_164234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164279 : List Nat := [1, 1, 3, 1, 3, 3, 4, 1, 3]
def baseStart_164279 : Nat := 118140960795 + 164279 * 2 ^ 59
def prefixEnd_164279 : Nat := 4983230072969 + 3 ^ 40 * 164279 * 2
def baseEnd_164279 : Nat := 74981411946727103428445

theorem tailTrace_164279 : CollatzResearch.WordTrace tailWord_164279 prefixEnd_164279 74981411946727103428445 := by
  unfold tailWord_164279
  simp only [CollatzResearch.WordTrace]
  refine ⟨5991747371852714464607891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3994498247901809643071927 5991747371852714464607891)
  ·
    refine ⟨8987621057779071696911837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5991747371852714464607891 8987621057779071696911837)
    ·
      refine ⟨3370357896667151886341939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8987621057779071696911837 3370357896667151886341939)
      ·
        refine ⟨5055536845000727829512909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370357896667151886341939 5055536845000727829512909)
        ·
          refine ⟨1895826316875272936067341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5055536845000727829512909 1895826316875272936067341)
          ·
            refine ⟨710934868828227351025253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1895826316875272936067341 710934868828227351025253)
            ·
              refine ⟨133300287905292628317235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 710934868828227351025253 133300287905292628317235)
              ·
                refine ⟨199950431857938942475853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133300287905292628317235 199950431857938942475853)
                ·
                  refine ⟨74981411946727103428445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199950431857938942475853 74981411946727103428445)
                  ·
                    rfl

theorem cell20_164279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 4, 1, 3].length) (baseStart_164279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164279 prefixEnd_164279 := by exact prefixLift 164279
  have htrace : WordTrace (prefixWord ++ tailWord_164279) baseStart_164279 baseEnd_164279 := by
    simpa [prefixWord, tailWord_164279, baseEnd_164279] using wordTrace_append hprefix tailTrace_164279
  have hstable : (prefixWord ++ tailWord_164279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164279).length < 2 ^ (prefixWord ++ tailWord_164279).sum := by decide
  have hdescent : baseEnd_164279 < baseStart_164279 := by decide
  rcases family_descends (prefixWord ++ tailWord_164279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164317 : List Nat := [1, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_164317 : Nat := 118140960795 + 164317 * 2 ^ 59
def prefixEnd_164317 : Nat := 4983230072969 + 3 ^ 40 * 164317 * 2
def baseEnd_164317 : Nat := 74998756182167860161623

theorem tailTrace_164317 : CollatzResearch.WordTrace tailWord_164317 prefixEnd_164317 74998756182167860161623 := by
  unfold tailWord_164317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5993133345715046954491205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3995422230476697969660803 5993133345715046954491205)
  ·
    refine ⟨1123712502321571303967101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5993133345715046954491205 1123712502321571303967101)
    ·
      refine ⟨421392188370589238987663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1123712502321571303967101 421392188370589238987663)
      ·
        refine ⟨632088282555883858481495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421392188370589238987663 632088282555883858481495)
        ·
          refine ⟨948132423833825787722243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632088282555883858481495 948132423833825787722243)
          ·
            refine ⟨1422198635750738681583365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948132423833825787722243 1422198635750738681583365)
            ·
              refine ⟨266662244203263502796881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1422198635750738681583365 266662244203263502796881)
              ·
                refine ⟨199996683152447627097661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266662244203263502796881 199996683152447627097661)
                ·
                  refine ⟨74998756182167860161623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 199996683152447627097661 74998756182167860161623)
                  ·
                    rfl

theorem cell20_164317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_164317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164317 prefixEnd_164317 := by exact prefixLift 164317
  have htrace : WordTrace (prefixWord ++ tailWord_164317) baseStart_164317 baseEnd_164317 := by
    simpa [prefixWord, tailWord_164317, baseEnd_164317] using wordTrace_append hprefix tailTrace_164317
  have hstable : (prefixWord ++ tailWord_164317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164317).length < 2 ^ (prefixWord ++ tailWord_164317).sum := by decide
  have hdescent : baseEnd_164317 < baseStart_164317 := by decide
  rcases family_descends (prefixWord ++ tailWord_164317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164341 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_164341 : Nat := 118140960795 + 164341 * 2 ^ 59
def prefixEnd_164341 : Nat := 4983230072969 + 3 ^ 40 * 164341 * 2
def baseEnd_164341 : Nat := 75009710436130443361525

theorem tailTrace_164341 : CollatzResearch.WordTrace tailWord_164341 prefixEnd_164341 75009710436130443361525 := by
  unfold tailWord_164341
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994008697628099053364877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3996005798418732702243251 5994008697628099053364877)
  ·
    refine ⟨2247753261610537145011829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5994008697628099053364877 2247753261610537145011829)
    ·
      refine ⟨210726868275987857344859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2247753261610537145011829 210726868275987857344859)
      ·
        refine ⟨316090302413981786017289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210726868275987857344859 316090302413981786017289)
        ·
          refine ⟨237067726810486339512967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316090302413981786017289 237067726810486339512967)
          ·
            refine ⟨355601590215729509269451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237067726810486339512967 355601590215729509269451)
            ·
              refine ⟨533402385323594263904177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355601590215729509269451 533402385323594263904177)
              ·
                refine ⟨400051788992695697928133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 533402385323594263904177 400051788992695697928133)
                ·
                  refine ⟨75009710436130443361525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400051788992695697928133 75009710436130443361525)
                  ·
                    rfl

theorem cell20_164341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_164341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164341 prefixEnd_164341 := by exact prefixLift 164341
  have htrace : WordTrace (prefixWord ++ tailWord_164341) baseStart_164341 baseEnd_164341 := by
    simpa [prefixWord, tailWord_164341, baseEnd_164341] using wordTrace_append hprefix tailTrace_164341
  have hstable : (prefixWord ++ tailWord_164341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164341).length < 2 ^ (prefixWord ++ tailWord_164341).sum := by decide
  have hdescent : baseEnd_164341 < baseStart_164341 := by decide
  rcases family_descends (prefixWord ++ tailWord_164341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164372 : List Nat := [2, 4, 3, 1, 1, 1, 3, 2, 3]
def baseStart_164372 : Nat := 118140960795 + 164372 * 2 ^ 59
def prefixEnd_164372 : Nat := 4983230072969 + 3 ^ 40 * 164372 * 2
def baseEnd_164372 : Nat := 75023859680832113328065

theorem tailTrace_164372 : CollatzResearch.WordTrace tailWord_164372 prefixEnd_164372 75023859680832113328065 := by
  unfold tailWord_164372
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997569680257895673871685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3996759573677194231828913 2997569680257895673871685)
  ·
    refine ⟨562044315048355438850941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2997569680257895673871685 562044315048355438850941)
    ·
      refine ⟨210766618143133289569103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 562044315048355438850941 210766618143133289569103)
      ·
        refine ⟨316149927214699934353655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210766618143133289569103 316149927214699934353655)
        ·
          refine ⟨474224890822049901530483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316149927214699934353655 474224890822049901530483)
          ·
            refine ⟨711337336233074852295725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 474224890822049901530483 711337336233074852295725)
            ·
              refine ⟨266751501087403069610897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711337336233074852295725 266751501087403069610897)
              ·
                refine ⟨200063625815552302208173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266751501087403069610897 200063625815552302208173)
                ·
                  refine ⟨75023859680832113328065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200063625815552302208173 75023859680832113328065)
                  ·
                    rfl

theorem cell20_164372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_164372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164372 prefixEnd_164372 := by exact prefixLift 164372
  have htrace : WordTrace (prefixWord ++ tailWord_164372) baseStart_164372 baseEnd_164372 := by
    simpa [prefixWord, tailWord_164372, baseEnd_164372] using wordTrace_append hprefix tailTrace_164372
  have hstable : (prefixWord ++ tailWord_164372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164372).length < 2 ^ (prefixWord ++ tailWord_164372).sum := by decide
  have hdescent : baseEnd_164372 < baseStart_164372 := by decide
  rcases family_descends (prefixWord ++ tailWord_164372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164376 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_164376 : Nat := 118140960795 + 164376 * 2 ^ 59
def prefixEnd_164376 : Nat := 4983230072969 + 3 ^ 40 * 164376 * 2
def baseEnd_164376 : Nat := 75025685389825877194715

theorem tailTrace_164376 : CollatzResearch.WordTrace tailWord_164376 prefixEnd_164376 75025685389825877194715 := by
  unfold tailWord_164376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2997642626250650015444491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3996856835000866687259321 2997642626250650015444491)
  ·
    refine ⟨4496463939375975023166737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2997642626250650015444491 4496463939375975023166737)
    ·
      refine ⟨3372347954531981267375053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4496463939375975023166737 3372347954531981267375053)
      ·
        refine ⟨1264630482949492975265645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3372347954531981267375053 1264630482949492975265645)
        ·
          refine ⟨474236431106059865724617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1264630482949492975265645 474236431106059865724617)
          ·
            refine ⟨355677323329544899293463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 474236431106059865724617 355677323329544899293463)
            ·
              refine ⟨533515984994317348940195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 355677323329544899293463 533515984994317348940195)
              ·
                refine ⟨800273977491476023410293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 533515984994317348940195 800273977491476023410293)
                ·
                  refine ⟨75025685389825877194715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800273977491476023410293 75025685389825877194715)
                  ·
                    rfl

theorem cell20_164376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_164376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164376 prefixEnd_164376 := by exact prefixLift 164376
  have htrace : WordTrace (prefixWord ++ tailWord_164376) baseStart_164376 baseEnd_164376 := by
    simpa [prefixWord, tailWord_164376, baseEnd_164376] using wordTrace_append hprefix tailTrace_164376
  have hstable : (prefixWord ++ tailWord_164376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164376).length < 2 ^ (prefixWord ++ tailWord_164376).sum := by decide
  have hdescent : baseEnd_164376 < baseStart_164376 := by decide
  rcases family_descends (prefixWord ++ tailWord_164376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164417 : List Nat := [1, 2, 5, 1, 1, 2, 3, 3, 2]
def baseStart_164417 : Nat := 118140960795 + 164417 * 2 ^ 59
def prefixEnd_164417 : Nat := 4983230072969 + 3 ^ 40 * 164417 * 2
def baseEnd_164417 : Nat := 75044398907011956827881

theorem tailTrace_164417 : CollatzResearch.WordTrace tailWord_164417 prefixEnd_164417 75044398907011956827881 := by
  unfold tailWord_164417
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996780645352764033131505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3997853763568509355421003 5996780645352764033131505)
  ·
    refine ⟨4497585484014573024848629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5996780645352764033131505 4497585484014573024848629)
    ·
      refine ⟨421648639126366221079559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4497585484014573024848629 421648639126366221079559)
      ·
        refine ⟨632472958689549331619339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 421648639126366221079559 632472958689549331619339)
        ·
          refine ⟨948709438034323997429009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 632472958689549331619339 948709438034323997429009)
          ·
            refine ⟨711532078525742998071757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 948709438034323997429009 711532078525742998071757)
            ·
              refine ⟨266824529447153624276909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 711532078525742998071757 266824529447153624276909)
              ·
                refine ⟨100059198542682609103841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 266824529447153624276909 100059198542682609103841)
                ·
                  refine ⟨75044398907011956827881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100059198542682609103841 75044398907011956827881)
                  ·
                    rfl

theorem cell20_164417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 3, 3, 2].length) (baseStart_164417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164417 prefixEnd_164417 := by exact prefixLift 164417
  have htrace : WordTrace (prefixWord ++ tailWord_164417) baseStart_164417 baseEnd_164417 := by
    simpa [prefixWord, tailWord_164417, baseEnd_164417] using wordTrace_append hprefix tailTrace_164417
  have hstable : (prefixWord ++ tailWord_164417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164417).length < 2 ^ (prefixWord ++ tailWord_164417).sum := by decide
  have hdescent : baseEnd_164417 < baseStart_164417 := by decide
  rcases family_descends (prefixWord ++ tailWord_164417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164420 : List Nat := [2, 3, 5, 1, 2, 1, 6]
def baseStart_164420 : Nat := 118140960795 + 164420 * 2 ^ 59
def prefixEnd_164420 : Nat := 4983230072969 + 3 ^ 40 * 164420 * 2
def baseEnd_164420 : Nat := 8338418687639697747541

theorem tailTrace_164420 : CollatzResearch.WordTrace tailWord_164420 prefixEnd_164420 8338418687639697747541 := by
  unfold tailWord_164420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998445032170947772745357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3997926709561263696993809 2998445032170947772745357)
  ·
    refine ⟨1124416887064105414779509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2998445032170947772745357 1124416887064105414779509)
    ·
      refine ⟨105414083162259882635579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1124416887064105414779509 105414083162259882635579)
      ·
        refine ⟨158121124743389823953369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105414083162259882635579 158121124743389823953369)
        ·
          refine ⟨118590843557542367965027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158121124743389823953369 118590843557542367965027)
          ·
            refine ⟨177886265336313551947541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118590843557542367965027 177886265336313551947541)
            ·
              refine ⟨8338418687639697747541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 177886265336313551947541 8338418687639697747541)
              ·
                rfl

theorem cell20_164420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 6].length) (baseStart_164420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164420 prefixEnd_164420 := by exact prefixLift 164420
  have htrace : WordTrace (prefixWord ++ tailWord_164420) baseStart_164420 baseEnd_164420 := by
    simpa [prefixWord, tailWord_164420, baseEnd_164420] using wordTrace_append hprefix tailTrace_164420
  have hstable : (prefixWord ++ tailWord_164420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164420).length < 2 ^ (prefixWord ++ tailWord_164420).sum := by decide
  have hdescent : baseEnd_164420 < baseStart_164420 := by decide
  rcases family_descends (prefixWord ++ tailWord_164420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164452 : List Nat := [2, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_164452 : Nat := 118140960795 + 164452 * 2 ^ 59
def prefixEnd_164452 : Nat := 4983230072969 + 3 ^ 40 * 164452 * 2
def baseEnd_164452 : Nat := 75060373860707390661071

theorem tailTrace_164452 : CollatzResearch.WordTrace tailWord_164452 prefixEnd_164452 75060373860707390661071 := by
  unfold tailWord_164452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999028600112982505327805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3998704800150643340437073 2999028600112982505327805)
  ·
    refine ⟨1124635725042368439497927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2999028600112982505327805 1124635725042368439497927)
    ·
      refine ⟨1686953587563552659246891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124635725042368439497927 1686953587563552659246891)
      ·
        refine ⟨2530430381345328988870337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686953587563552659246891 2530430381345328988870337)
        ·
          refine ⟨1897822786008996741652753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530430381345328988870337 1897822786008996741652753)
          ·
            refine ⟨1423367089506747556239565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897822786008996741652753 1423367089506747556239565)
            ·
              refine ⟨533762658565030333589837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1423367089506747556239565 533762658565030333589837)
              ·
                refine ⟨200160996961886375096189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 533762658565030333589837 200160996961886375096189)
                ·
                  refine ⟨75060373860707390661071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200160996961886375096189 75060373860707390661071)
                  ·
                    rfl

theorem cell20_164452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_164452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164452 prefixEnd_164452 := by exact prefixLift 164452
  have htrace : WordTrace (prefixWord ++ tailWord_164452) baseStart_164452 baseEnd_164452 := by
    simpa [prefixWord, tailWord_164452, baseEnd_164452] using wordTrace_append hprefix tailTrace_164452
  have hstable : (prefixWord ++ tailWord_164452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164452).length < 2 ^ (prefixWord ++ tailWord_164452).sum := by decide
  have hdescent : baseEnd_164452 < baseStart_164452 := by decide
  rcases family_descends (prefixWord ++ tailWord_164452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164482 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_164482 : Nat := 118140960795 + 164482 * 2 ^ 59
def prefixEnd_164482 : Nat := 4983230072969 + 3 ^ 40 * 164482 * 2
def baseEnd_164482 : Nat := 75074066678160619660949

theorem tailTrace_164482 : CollatzResearch.WordTrace tailWord_164482 prefixEnd_164482 75074066678160619660949 := by
  unfold tailWord_164482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499787847529320033561925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3999434260078186756165133 1499787847529320033561925)
  ·
    refine ⟨281210221411747506292861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1499787847529320033561925 281210221411747506292861)
    ·
      refine ⟨105453833029405314859823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 281210221411747506292861 105453833029405314859823)
      ·
        refine ⟨158180749544107972289735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105453833029405314859823 158180749544107972289735)
        ·
          refine ⟨237271124316161958434603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158180749544107972289735 237271124316161958434603)
          ·
            refine ⟨355906686474242937651905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237271124316161958434603 355906686474242937651905)
            ·
              refine ⟨266930014855682203238929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 355906686474242937651905 266930014855682203238929)
              ·
                refine ⟨200197511141761652429197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266930014855682203238929 200197511141761652429197)
                ·
                  refine ⟨75074066678160619660949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200197511141761652429197 75074066678160619660949)
                  ·
                    rfl

theorem cell20_164482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_164482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164482 prefixEnd_164482 := by exact prefixLift 164482
  have htrace : WordTrace (prefixWord ++ tailWord_164482) baseStart_164482 baseEnd_164482 := by
    simpa [prefixWord, tailWord_164482, baseEnd_164482] using wordTrace_append hprefix tailTrace_164482
  have hstable : (prefixWord ++ tailWord_164482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164482).length < 2 ^ (prefixWord ++ tailWord_164482).sum := by decide
  have hdescent : baseEnd_164482 < baseStart_164482 := by decide
  rcases family_descends (prefixWord ++ tailWord_164482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164500 : List Nat := [2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_164500 : Nat := 118140960795 + 164500 * 2 ^ 59
def prefixEnd_164500 : Nat := 4983230072969 + 3 ^ 40 * 164500 * 2
def baseEnd_164500 : Nat := 25027427456210852353625

theorem tailTrace_164500 : CollatzResearch.WordTrace tailWord_164500 prefixEnd_164500 25027427456210852353625 := by
  unfold tailWord_164500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2999903952026034604201477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3999871936034712805601969 2999903952026034604201477)
  ·
    refine ⟨562481991004881488287777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2999903952026034604201477 562481991004881488287777)
    ·
      refine ⟨421861493253661116215833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 562481991004881488287777 421861493253661116215833)
      ·
        refine ⟨316396119940245837161875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 421861493253661116215833 316396119940245837161875)
        ·
          refine ⟨474594179910368755742813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 316396119940245837161875 474594179910368755742813)
          ·
            refine ⟨177972817466388283403555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 474594179910368755742813 177972817466388283403555)
            ·
              refine ⟨266959226199582425105333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177972817466388283403555 266959226199582425105333)
              ·
                refine ⟨25027427456210852353625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 266959226199582425105333 25027427456210852353625)
                ·
                  rfl

theorem cell20_164500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_164500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164500 prefixEnd_164500 := by exact prefixLift 164500
  have htrace : WordTrace (prefixWord ++ tailWord_164500) baseStart_164500 baseEnd_164500 := by
    simpa [prefixWord, tailWord_164500, baseEnd_164500] using wordTrace_append hprefix tailTrace_164500
  have hstable : (prefixWord ++ tailWord_164500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164500).length < 2 ^ (prefixWord ++ tailWord_164500).sum := by decide
  have hdescent : baseEnd_164500 < baseStart_164500 := by decide
  rcases family_descends (prefixWord ++ tailWord_164500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164542 : List Nat := [4, 2, 1, 1, 2, 1, 9]
def baseStart_164542 : Nat := 118140960795 + 164542 * 2 ^ 59
def prefixEnd_164542 : Nat := 4983230072969 + 3 ^ 40 * 164542 * 2
def baseEnd_164542 : Nat := 8344605812563008628967

theorem tailTrace_164542 : CollatzResearch.WordTrace tailWord_164542 prefixEnd_164542 8344605812563008628967 := by
  unfold tailWord_164542
  simp only [CollatzResearch.WordTrace]
  refine ⟨750167471237488797678985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4000893179933273587621253 750167471237488797678985)
  ·
    refine ⟨562625603428116598259239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 750167471237488797678985 562625603428116598259239)
    ·
      refine ⟨843938405142174897388859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 562625603428116598259239 843938405142174897388859)
      ·
        refine ⟨1265907607713262346083289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843938405142174897388859 1265907607713262346083289)
        ·
          refine ⟨949430705784946759562467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265907607713262346083289 949430705784946759562467)
          ·
            refine ⟨1424146058677420139343701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949430705784946759562467 1424146058677420139343701)
            ·
              refine ⟨8344605812563008628967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1424146058677420139343701 8344605812563008628967)
              ·
                rfl

theorem cell20_164542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_164542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164542 prefixEnd_164542 := by exact prefixLift 164542
  have htrace : WordTrace (prefixWord ++ tailWord_164542) baseStart_164542 baseEnd_164542 := by
    simpa [prefixWord, tailWord_164542, baseEnd_164542] using wordTrace_append hprefix tailTrace_164542
  have hstable : (prefixWord ++ tailWord_164542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164542).length < 2 ^ (prefixWord ++ tailWord_164542).sum := by decide
  have hdescent : baseEnd_164542 < baseStart_164542 := by decide
  rcases family_descends (prefixWord ++ tailWord_164542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164552 : List Nat := [2, 1, 3, 1, 2, 3, 2, 4, 2]
def baseStart_164552 : Nat := 118140960795 + 164552 * 2 ^ 59
def prefixEnd_164552 : Nat := 4983230072969 + 3 ^ 40 * 164552 * 2
def baseEnd_164552 : Nat := 75106016585551487327329

theorem tailTrace_164552 : CollatzResearch.WordTrace tailWord_164552 prefixEnd_164552 75106016585551487327329 := by
  unfold tailWord_164552
  simp only [CollatzResearch.WordTrace]
  refine ⟨3000852249931841044647955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4001136333242454726197273 3000852249931841044647955)
  ·
    refine ⟨4501278374897761566971933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3000852249931841044647955 4501278374897761566971933)
    ·
      refine ⟨1687979390586660587614475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4501278374897761566971933 1687979390586660587614475)
      ·
        refine ⟨2531969085879990881421713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1687979390586660587614475 2531969085879990881421713)
        ·
          refine ⟨1898976814409993161066285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2531969085879990881421713 1898976814409993161066285)
          ·
            refine ⟨712116305403747435399857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1898976814409993161066285 712116305403747435399857)
            ·
              refine ⟨534087229052810576549893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 712116305403747435399857 534087229052810576549893)
              ·
                refine ⟨100141355447401983103105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534087229052810576549893 100141355447401983103105)
                ·
                  refine ⟨75106016585551487327329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100141355447401983103105 75106016585551487327329)
                  ·
                    rfl

theorem cell20_164552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_164552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164552 prefixEnd_164552 := by exact prefixLift 164552
  have htrace : WordTrace (prefixWord ++ tailWord_164552) baseStart_164552 baseEnd_164552 := by
    simpa [prefixWord, tailWord_164552, baseEnd_164552] using wordTrace_append hprefix tailTrace_164552
  have hstable : (prefixWord ++ tailWord_164552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164552).length < 2 ^ (prefixWord ++ tailWord_164552).sum := by decide
  have hdescent : baseEnd_164552 < baseStart_164552 := by decide
  rcases family_descends (prefixWord ++ tailWord_164552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164562 : List Nat := [3, 2, 2, 2, 3, 1, 3, 1, 3]
def baseStart_164562 : Nat := 118140960795 + 164562 * 2 ^ 59
def prefixEnd_164562 : Nat := 4983230072969 + 3 ^ 40 * 164562 * 2
def baseEnd_164562 : Nat := 75110580858035896993955

theorem tailTrace_164562 : CollatzResearch.WordTrace tailWord_164562 prefixEnd_164562 75110580858035896993955 := by
  unfold tailWord_164562
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500517307456863449289985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4001379486551635864773293 1500517307456863449289985)
  ·
    refine ⟨1125387980592647586967489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1500517307456863449289985 1125387980592647586967489)
    ·
      refine ⟨844040985444485690225617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1125387980592647586967489 844040985444485690225617)
      ·
        refine ⟨633030739083364267669213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 844040985444485690225617 633030739083364267669213)
        ·
          refine ⟨237386527156261600375955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 633030739083364267669213 237386527156261600375955)
          ·
            refine ⟨356079790734392400563933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237386527156261600375955 356079790734392400563933)
            ·
              refine ⟨133529921525397150211475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 356079790734392400563933 133529921525397150211475)
              ·
                refine ⟨200294882288095725317213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133529921525397150211475 200294882288095725317213)
                ·
                  refine ⟨75110580858035896993955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200294882288095725317213 75110580858035896993955)
                  ·
                    rfl

theorem cell20_164562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_164562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164562 prefixEnd_164562 := by exact prefixLift 164562
  have htrace : WordTrace (prefixWord ++ tailWord_164562) baseStart_164562 baseEnd_164562 := by
    simpa [prefixWord, tailWord_164562, baseEnd_164562] using wordTrace_append hprefix tailTrace_164562
  have hstable : (prefixWord ++ tailWord_164562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164562).length < 2 ^ (prefixWord ++ tailWord_164562).sum := by decide
  have hdescent : baseEnd_164562 < baseStart_164562 := by decide
  rcases family_descends (prefixWord ++ tailWord_164562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164580 : List Nat := [2, 3, 1, 1, 1, 5, 1, 6]
def baseStart_164580 : Nat := 118140960795 + 164580 * 2 ^ 59
def prefixEnd_164580 : Nat := 4983230072969 + 3 ^ 40 * 164580 * 2
def baseEnd_164580 : Nat := 25039598849502611464627

theorem tailTrace_164580 : CollatzResearch.WordTrace tailWord_164580 prefixEnd_164580 25039598849502611464627 := by
  unfold tailWord_164580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3001362871881121435657597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4001817162508161914210129 3001362871881121435657597)
  ·
    refine ⟨1125511076955420538371599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3001362871881121435657597 1125511076955420538371599)
    ·
      refine ⟨1688266615433130807557399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125511076955420538371599 1688266615433130807557399)
      ·
        refine ⟨2532399923149696211336099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688266615433130807557399 2532399923149696211336099)
        ·
          refine ⟨3798599884724544317004149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532399923149696211336099 3798599884724544317004149)
          ·
            refine ⟨356118739192926029719139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3798599884724544317004149 356118739192926029719139)
            ·
              refine ⟨534178108789389044578709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356118739192926029719139 534178108789389044578709)
              ·
                refine ⟨25039598849502611464627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 534178108789389044578709 25039598849502611464627)
                ·
                  rfl

theorem cell20_164580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_164580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164580 prefixEnd_164580 := by exact prefixLift 164580
  have htrace : WordTrace (prefixWord ++ tailWord_164580) baseStart_164580 baseEnd_164580 := by
    simpa [prefixWord, tailWord_164580, baseEnd_164580] using wordTrace_append hprefix tailTrace_164580
  have hstable : (prefixWord ++ tailWord_164580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164580).length < 2 ^ (prefixWord ++ tailWord_164580).sum := by decide
  have hdescent : baseEnd_164580 < baseStart_164580 := by decide
  rcases family_descends (prefixWord ++ tailWord_164580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164618 : List Nat := [3, 1, 2, 2, 1, 2, 4, 5]
def baseStart_164618 : Nat := 118140960795 + 164618 * 2 ^ 59
def prefixEnd_164618 : Nat := 4983230072969 + 3 ^ 40 * 164618 * 2
def baseEnd_164618 : Nat := 25045380261316197042353

theorem tailTrace_164618 : CollatzResearch.WordTrace tailWord_164618 prefixEnd_164618 25045380261316197042353 := by
  unfold tailWord_164618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501027929406143840299627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4002741145083050240799005 1501027929406143840299627)
  ·
    refine ⟨2251541894109215760449441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1501027929406143840299627 2251541894109215760449441)
    ·
      refine ⟨1688656420581911820337081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2251541894109215760449441 1688656420581911820337081)
      ·
        refine ⟨1266492315436433865252811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1688656420581911820337081 1266492315436433865252811)
        ·
          refine ⟨1899738473154650797879217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266492315436433865252811 1899738473154650797879217)
          ·
            refine ⟨1424803854865988098409413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899738473154650797879217 1424803854865988098409413)
            ·
              refine ⟨267150722787372768451765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1424803854865988098409413 267150722787372768451765)
              ·
                refine ⟨25045380261316197042353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 267150722787372768451765 25045380261316197042353)
                ·
                  rfl

theorem cell20_164618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_164618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164618 prefixEnd_164618 := by exact prefixLift 164618
  have htrace : WordTrace (prefixWord ++ tailWord_164618) baseStart_164618 baseEnd_164618 := by
    simpa [prefixWord, tailWord_164618, baseEnd_164618] using wordTrace_append hprefix tailTrace_164618
  have hstable : (prefixWord ++ tailWord_164618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164618).length < 2 ^ (prefixWord ++ tailWord_164618).sum := by decide
  have hdescent : baseEnd_164618 < baseStart_164618 := by decide
  rcases family_descends (prefixWord ++ tailWord_164618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164632 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_164632 : Nat := 118140960795 + 164632 * 2 ^ 59
def prefixEnd_164632 : Nat := 4983230072969 + 3 ^ 40 * 164632 * 2
def baseEnd_164632 : Nat := 75142530765426764660335

theorem tailTrace_164632 : CollatzResearch.WordTrace tailWord_164632 prefixEnd_164632 75142530765426764660335 := by
  unfold tailWord_164632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002311169786927876104075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4003081559715903834805433 3002311169786927876104075)
  ·
    refine ⟨4503466754680391814156113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002311169786927876104075 4503466754680391814156113)
    ·
      refine ⟨3377600066010293860617085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503466754680391814156113 3377600066010293860617085)
      ·
        refine ⟨1266600024753860197731407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3377600066010293860617085 1266600024753860197731407)
        ·
          refine ⟨1899900037130790296597111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266600024753860197731407 1899900037130790296597111)
          ·
            refine ⟨2849850055696185444895667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899900037130790296597111 2849850055696185444895667)
            ·
              refine ⟨4274775083544278167343501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849850055696185444895667 4274775083544278167343501)
              ·
                refine ⟨1603040656329104312753813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4274775083544278167343501 1603040656329104312753813)
                ·
                  refine ⟨75142530765426764660335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1603040656329104312753813 75142530765426764660335)
                  ·
                    rfl

theorem cell20_164632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_164632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164632 prefixEnd_164632 := by exact prefixLift 164632
  have htrace : WordTrace (prefixWord ++ tailWord_164632) baseStart_164632 baseEnd_164632 := by
    simpa [prefixWord, tailWord_164632, baseEnd_164632] using wordTrace_append hprefix tailTrace_164632
  have hstable : (prefixWord ++ tailWord_164632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164632).length < 2 ^ (prefixWord ++ tailWord_164632).sum := by decide
  have hdescent : baseEnd_164632 < baseStart_164632 := by decide
  rcases family_descends (prefixWord ++ tailWord_164632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164662 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_164662 : Nat := 118140960795 + 164662 * 2 ^ 59
def prefixEnd_164662 : Nat := 4983230072969 + 3 ^ 40 * 164662 * 2
def baseEnd_164662 : Nat := 75156223582879993660213

theorem tailTrace_164662 : CollatzResearch.WordTrace tailWord_164662 prefixEnd_164662 75156223582879993660213 := by
  unfold tailWord_164662
  simp only [CollatzResearch.WordTrace]
  refine ⟨375357283091573179737515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4003811019643447250533493 375357283091573179737515)
  ·
    refine ⟨563035924637359769606273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375357283091573179737515 563035924637359769606273)
    ·
      refine ⟨422276943478019827204705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 563035924637359769606273 422276943478019827204705)
      ·
        refine ⟨316707707608514870403529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 422276943478019827204705 316707707608514870403529)
        ·
          refine ⟨237530780706386152802647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316707707608514870403529 237530780706386152802647)
          ·
            refine ⟨356296171059579229203971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237530780706386152802647 356296171059579229203971)
            ·
              refine ⟨534444256589368843805957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 356296171059579229203971 534444256589368843805957)
              ·
                refine ⟨100208298110506658213617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 534444256589368843805957 100208298110506658213617)
                ·
                  refine ⟨75156223582879993660213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100208298110506658213617 75156223582879993660213)
                  ·
                    rfl

theorem cell20_164662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_164662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164662 prefixEnd_164662 := by exact prefixLift 164662
  have htrace : WordTrace (prefixWord ++ tailWord_164662) baseStart_164662 baseEnd_164662 := by
    simpa [prefixWord, tailWord_164662, baseEnd_164662] using wordTrace_append hprefix tailTrace_164662
  have hstable : (prefixWord ++ tailWord_164662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164662).length < 2 ^ (prefixWord ++ tailWord_164662).sum := by decide
  have hdescent : baseEnd_164662 < baseStart_164662 := by decide
  rcases family_descends (prefixWord ++ tailWord_164662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164677 : List Nat := [1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_164677 : Nat := 118140960795 + 164677 * 2 ^ 59
def prefixEnd_164677 : Nat := 4983230072969 + 3 ^ 40 * 164677 * 2
def baseEnd_164677 : Nat := 25054356663868869386717

theorem tailTrace_164677 : CollatzResearch.WordTrace tailWord_164677 prefixEnd_164677 25054356663868869386717 := by
  unfold tailWord_164677
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006263624410828437596285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4004175749607218958397523 6006263624410828437596285)
  ·
    refine ⟨2252348859154060664098607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6006263624410828437596285 2252348859154060664098607)
    ·
      refine ⟨3378523288731090996147911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252348859154060664098607 3378523288731090996147911)
      ·
        refine ⟨5067784933096636494221867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378523288731090996147911 5067784933096636494221867)
        ·
          refine ⟨7601677399644954741332801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067784933096636494221867 7601677399644954741332801)
          ·
            refine ⟨5701258049733716055999601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7601677399644954741332801 5701258049733716055999601)
            ·
              refine ⟨4275943537300287041999701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701258049733716055999601 4275943537300287041999701)
              ·
                refine ⟨25054356663868869386717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4275943537300287041999701 25054356663868869386717)
                ·
                  rfl

theorem cell20_164677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_164677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164677 prefixEnd_164677 := by exact prefixLift 164677
  have htrace : WordTrace (prefixWord ++ tailWord_164677) baseStart_164677 baseEnd_164677 := by
    simpa [prefixWord, tailWord_164677, baseEnd_164677] using wordTrace_append hprefix tailTrace_164677
  have hstable : (prefixWord ++ tailWord_164677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164677).length < 2 ^ (prefixWord ++ tailWord_164677).sum := by decide
  have hdescent : baseEnd_164677 < baseStart_164677 := by decide
  rcases family_descends (prefixWord ++ tailWord_164677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164704 : List Nat := [2, 1, 1, 3, 3, 1, 4, 3, 2]
def baseStart_164704 : Nat := 118140960795 + 164704 * 2 ^ 59
def prefixEnd_164704 : Nat := 4983230072969 + 3 ^ 40 * 164704 * 2
def baseEnd_164704 : Nat := 75175393527314514260041

theorem tailTrace_164704 : CollatzResearch.WordTrace tailWord_164704 prefixEnd_164704 75175393527314514260041 := by
  unfold tailWord_164704
  simp only [CollatzResearch.WordTrace]
  refine ⟨3003624197656506024414583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4004832263542008032552777 3003624197656506024414583)
  ·
    refine ⟨4505436296484759036621875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3003624197656506024414583 4505436296484759036621875)
    ·
      refine ⟨6758154444727138554932813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4505436296484759036621875 6758154444727138554932813)
      ·
        refine ⟨2534307916772676958099805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6758154444727138554932813 2534307916772676958099805)
        ·
          refine ⟨950365468789753859287427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2534307916772676958099805 950365468789753859287427)
          ·
            refine ⟨1425548203184630788931141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950365468789753859287427 1425548203184630788931141)
            ·
              refine ⟨267290288097118272924589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1425548203184630788931141 267290288097118272924589)
              ·
                refine ⟨100233858036419352346721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267290288097118272924589 100233858036419352346721)
                ·
                  refine ⟨75175393527314514260041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100233858036419352346721 75175393527314514260041)
                  ·
                    rfl

theorem cell20_164704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_164704 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164704 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164704 prefixEnd_164704 := by exact prefixLift 164704
  have htrace : WordTrace (prefixWord ++ tailWord_164704) baseStart_164704 baseEnd_164704 := by
    simpa [prefixWord, tailWord_164704, baseEnd_164704] using wordTrace_append hprefix tailTrace_164704
  have hstable : (prefixWord ++ tailWord_164704).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164704).length < 2 ^ (prefixWord ++ tailWord_164704).sum := by decide
  have hdescent : baseEnd_164704 < baseStart_164704 := by decide
  rcases family_descends (prefixWord ++ tailWord_164704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164725 : List Nat := [1, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_164725 : Nat := 118140960795 + 164725 * 2 ^ 59
def prefixEnd_164725 : Nat := 4983230072969 + 3 ^ 40 * 164725 * 2
def baseEnd_164725 : Nat := 75184978499531774559955

theorem tailTrace_164725 : CollatzResearch.WordTrace tailWord_164725 prefixEnd_164725 75184978499531774559955 := by
  unfold tailWord_164725
  simp only [CollatzResearch.WordTrace]
  refine ⟨6008014328236932635343629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4005342885491288423562419 6008014328236932635343629)
  ·
    refine ⟨2253005373088849738253861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6008014328236932635343629 2253005373088849738253861)
    ·
      refine ⟨422438507454159325922599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2253005373088849738253861 422438507454159325922599)
      ·
        refine ⟨633657761181238988883899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422438507454159325922599 633657761181238988883899)
        ·
          refine ⟨950486641771858483325849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 633657761181238988883899 950486641771858483325849)
          ·
            refine ⟨712864981328893862494387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 950486641771858483325849 712864981328893862494387)
            ·
              refine ⟨1069297471993340793741581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 712864981328893862494387 1069297471993340793741581)
              ·
                refine ⟨400986551997502797653093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1069297471993340793741581 400986551997502797653093)
                ·
                  refine ⟨75184978499531774559955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 400986551997502797653093 75184978499531774559955)
                  ·
                    rfl

theorem cell20_164725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_164725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164725 prefixEnd_164725 := by exact prefixLift 164725
  have htrace : WordTrace (prefixWord ++ tailWord_164725) baseStart_164725 baseEnd_164725 := by
    simpa [prefixWord, tailWord_164725, baseEnd_164725] using wordTrace_append hprefix tailTrace_164725
  have hstable : (prefixWord ++ tailWord_164725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164725).length < 2 ^ (prefixWord ++ tailWord_164725).sum := by decide
  have hdescent : baseEnd_164725 < baseStart_164725 := by decide
  rcases family_descends (prefixWord ++ tailWord_164725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164770 : List Nat := [3, 3, 1, 2, 2, 1, 8]
def baseStart_164770 : Nat := 118140960795 + 164770 * 2 ^ 59
def prefixEnd_164770 : Nat := 4983230072969 + 3 ^ 40 * 164770 * 2
def baseEnd_164770 : Nat := 8356168636190179784419

theorem tailTrace_164770 : CollatzResearch.WordTrace tailWord_164770 prefixEnd_164770 8356168636190179784419 := by
  unfold tailWord_164770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502413903268476330182941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4006437075382603547154509 1502413903268476330182941)
  ·
    refine ⟨563405213725678623818603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1502413903268476330182941 563405213725678623818603)
    ·
      refine ⟨845107820588517935727905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563405213725678623818603 845107820588517935727905)
      ·
        refine ⟨633830865441388451795929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 845107820588517935727905 633830865441388451795929)
        ·
          refine ⟨475373149081041338846947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 633830865441388451795929 475373149081041338846947)
          ·
            refine ⟨713059723621562008270421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 475373149081041338846947 713059723621562008270421)
            ·
              refine ⟨8356168636190179784419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 713059723621562008270421 8356168636190179784419)
              ·
                rfl

theorem cell20_164770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_164770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164770 prefixEnd_164770 := by exact prefixLift 164770
  have htrace : WordTrace (prefixWord ++ tailWord_164770) baseStart_164770 baseEnd_164770 := by
    simpa [prefixWord, tailWord_164770, baseEnd_164770] using wordTrace_append hprefix tailTrace_164770
  have hstable : (prefixWord ++ tailWord_164770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164770).length < 2 ^ (prefixWord ++ tailWord_164770).sum := by decide
  have hdescent : baseEnd_164770 < baseStart_164770 := by decide
  rcases family_descends (prefixWord ++ tailWord_164770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164777 : List Nat := [1, 2, 1, 1, 1, 1, 6, 4, 3]
def baseStart_164777 : Nat := 118140960795 + 164777 * 2 ^ 59
def prefixEnd_164777 : Nat := 4983230072969 + 3 ^ 40 * 164777 * 2
def baseEnd_164777 : Nat := 75208712716450704826409

theorem tailTrace_164777 : CollatzResearch.WordTrace tailWord_164777 prefixEnd_164777 75208712716450704826409 := by
  unfold tailWord_164777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6009910924048545516236585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4006607282699030344157723 6009910924048545516236585)
  ·
    refine ⟨4507433193036409137177439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6009910924048545516236585 4507433193036409137177439)
    ·
      refine ⟨6761149789554613705766159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4507433193036409137177439 6761149789554613705766159)
      ·
        refine ⟨10141724684331920558649239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761149789554613705766159 10141724684331920558649239)
        ·
          refine ⟨15212587026497880837973859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10141724684331920558649239 15212587026497880837973859)
          ·
            refine ⟨22818880539746821256960789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15212587026497880837973859 22818880539746821256960789)
            ·
              refine ⟨1069635025300632246420037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22818880539746821256960789 1069635025300632246420037)
              ·
                refine ⟨200556567243868546203757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1069635025300632246420037 200556567243868546203757)
                ·
                  refine ⟨75208712716450704826409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200556567243868546203757 75208712716450704826409)
                  ·
                    rfl

theorem cell20_164777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4, 3].length) (baseStart_164777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164777 prefixEnd_164777 := by exact prefixLift 164777
  have htrace : WordTrace (prefixWord ++ tailWord_164777) baseStart_164777 baseEnd_164777 := by
    simpa [prefixWord, tailWord_164777, baseEnd_164777] using wordTrace_append hprefix tailTrace_164777
  have hstable : (prefixWord ++ tailWord_164777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164777).length < 2 ^ (prefixWord ++ tailWord_164777).sum := by decide
  have hdescent : baseEnd_164777 < baseStart_164777 := by decide
  rcases family_descends (prefixWord ++ tailWord_164777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164791 : List Nat := [1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_164791 : Nat := 118140960795 + 164791 * 2 ^ 59
def prefixEnd_164791 : Nat := 4983230072969 + 3 ^ 40 * 164791 * 2
def baseEnd_164791 : Nat := 25071700899309626119895

theorem tailTrace_164791 : CollatzResearch.WordTrace tailWord_164791 prefixEnd_164791 25071700899309626119895 := by
  unfold tailWord_164791
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010421545997825907246227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4006947697331883938164151 6010421545997825907246227)
  ·
    refine ⟨9015632318996738860869341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6010421545997825907246227 9015632318996738860869341)
    ·
      refine ⟨3380862119623777072826003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9015632318996738860869341 3380862119623777072826003)
      ·
        refine ⟨5071293179435665609239005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3380862119623777072826003 5071293179435665609239005)
        ·
          refine ⟨1901734942288374603464627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5071293179435665609239005 1901734942288374603464627)
          ·
            refine ⟨2852602413432561905196941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901734942288374603464627 2852602413432561905196941)
            ·
              refine ⟨1069725905037210714448853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2852602413432561905196941 1069725905037210714448853)
              ·
                refine ⟨25071700899309626119895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1069725905037210714448853 25071700899309626119895)
                ·
                  rfl

theorem cell20_164791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_164791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164791 prefixEnd_164791 := by exact prefixLift 164791
  have htrace : WordTrace (prefixWord ++ tailWord_164791) baseStart_164791 baseEnd_164791 := by
    simpa [prefixWord, tailWord_164791, baseEnd_164791] using wordTrace_append hprefix tailTrace_164791
  have hstable : (prefixWord ++ tailWord_164791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164791).length < 2 ^ (prefixWord ++ tailWord_164791).sum := by decide
  have hdescent : baseEnd_164791 < baseStart_164791 := by decide
  rcases family_descends (prefixWord ++ tailWord_164791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
