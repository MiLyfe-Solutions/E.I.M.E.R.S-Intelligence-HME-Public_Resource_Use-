import V185TrunkScan23Chunk0568

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3364221 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_3364221 : Nat := 118140960795 + 3364221 * 2 ^ 59
def prefixEnd_3364221 : Nat := 4983230072969 + 3 ^ 40 * 3364221 * 2
def baseEnd_3364221 : Nat := 575820800316529067855245

theorem tailTrace_3364221 : CollatzResearch.WordTrace tailWord_3364221 prefixEnd_3364221 575820800316529067855245 := by
  unfold tailWord_3364221
  simp only [CollatzResearch.WordTrace]
  refine ⟨122703220345009355048596517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81802146896672903365731011 122703220345009355048596517)
  ·
    refine ⟨23006853814689254071611847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122703220345009355048596517 23006853814689254071611847)
    ·
      refine ⟨34510280722033881107417771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23006853814689254071611847 34510280722033881107417771)
      ·
        refine ⟨51765421083050821661126657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34510280722033881107417771 51765421083050821661126657)
        ·
          refine ⟨38824065812288116245844993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51765421083050821661126657 38824065812288116245844993)
          ·
            refine ⟨29118049359216087184383745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38824065812288116245844993 29118049359216087184383745)
            ·
              refine ⟨21838537019412065388287809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29118049359216087184383745 21838537019412065388287809)
              ·
                refine ⟨16378902764559049041215857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21838537019412065388287809 16378902764559049041215857)
                ·
                  refine ⟨12284177073419286780911893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16378902764559049041215857 12284177073419286780911893)
                  ·
                    refine ⟨575820800316529067855245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12284177073419286780911893 575820800316529067855245)
                    ·
                      rfl

theorem cell23_3364221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_3364221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364221 prefixEnd_3364221 := by exact prefixLift 3364221
  have htrace : WordTrace (prefixWord ++ tailWord_3364221) baseStart_3364221 baseEnd_3364221 := by
    simpa [prefixWord, tailWord_3364221, baseEnd_3364221] using wordTrace_append hprefix tailTrace_3364221
  have hstable : (prefixWord ++ tailWord_3364221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364221).length < 2 ^ (prefixWord ++ tailWord_3364221).sum := by decide
  have hdescent : baseEnd_3364221 < baseStart_3364221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364241 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3364241 : Nat := 118140960795 + 3364241 * 2 ^ 59
def prefixEnd_3364241 : Nat := 4983230072969 + 3 ^ 40 * 3364241 * 2
def baseEnd_3364241 : Nat := 1727472670562677125315643

theorem tailTrace_3364241 : CollatzResearch.WordTrace tailWord_3364241 prefixEnd_3364241 1727472670562677125315643 := by
  unfold tailWord_3364241
  simp only [CollatzResearch.WordTrace]
  refine ⟨122703949804936898464324577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81802633203291265642883051 122703949804936898464324577)
  ·
    refine ⟨92027962353702673848243433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122703949804936898464324577 92027962353702673848243433)
    ·
      refine ⟨69020971765277005386182575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92027962353702673848243433 69020971765277005386182575)
      ·
        refine ⟨103531457647915508079273863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69020971765277005386182575 103531457647915508079273863)
        ·
          refine ⟨155297186471873262118910795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103531457647915508079273863 155297186471873262118910795)
          ·
            refine ⟨232945779707809893178366193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155297186471873262118910795 232945779707809893178366193)
            ·
              refine ⟨174709334780857419883774645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232945779707809893178366193 174709334780857419883774645)
              ·
                refine ⟨16379000135705383114103873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174709334780857419883774645 16379000135705383114103873)
                ·
                  refine ⟨12284250101779037335577905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16379000135705383114103873 12284250101779037335577905)
                  ·
                    refine ⟨9213187576334278001683429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12284250101779037335577905 9213187576334278001683429)
                    ·
                      refine ⟨1727472670562677125315643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9213187576334278001683429 1727472670562677125315643)
                      ·
                        rfl

theorem cell23_3364241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3364241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364241 prefixEnd_3364241 := by exact prefixLift 3364241
  have htrace : WordTrace (prefixWord ++ tailWord_3364241) baseStart_3364241 baseEnd_3364241 := by
    simpa [prefixWord, tailWord_3364241, baseEnd_3364241] using wordTrace_append hprefix tailTrace_3364241
  have hstable : (prefixWord ++ tailWord_3364241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364241).length < 2 ^ (prefixWord ++ tailWord_3364241).sum := by decide
  have hdescent : baseEnd_3364241 < baseStart_3364241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364268 : List Nat := [2, 2, 1, 1, 1, 1, 5, 5, 5]
def baseStart_3364268 : Nat := 118140960795 + 3364268 * 2 ^ 59
def prefixEnd_3364268 : Nat := 4983230072969 + 3 ^ 40 * 3364268 * 2
def baseEnd_3364268 : Nat := 191942948282260946630891

theorem tailTrace_3364268 : CollatzResearch.WordTrace tailWord_3364268 prefixEnd_3364268 191942948282260946630891 := by
  unfold tailWord_3364268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61352467287919541037778729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81803289717226054717038305 61352467287919541037778729)
  ·
    refine ⟨46014350465939655778334047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61352467287919541037778729 46014350465939655778334047)
    ·
      refine ⟨69021525698909483667501071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46014350465939655778334047 69021525698909483667501071)
      ·
        refine ⟨103532288548364225501251607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69021525698909483667501071 103532288548364225501251607)
        ·
          refine ⟨155298432822546338251877411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103532288548364225501251607 155298432822546338251877411)
          ·
            refine ⟨232947649233819507377816117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155298432822546338251877411 232947649233819507377816117)
            ·
              refine ⟨21838842115670578816670261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232947649233819507377816117 21838842115670578816670261)
              ·
                refine ⟨2047391448344116764062837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21838842115670578816670261 2047391448344116764062837)
                ·
                  refine ⟨191942948282260946630891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2047391448344116764062837 191942948282260946630891)
                  ·
                    rfl

theorem cell23_3364268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_3364268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364268 prefixEnd_3364268 := by exact prefixLift 3364268
  have htrace : WordTrace (prefixWord ++ tailWord_3364268) baseStart_3364268 baseEnd_3364268 := by
    simpa [prefixWord, tailWord_3364268, baseEnd_3364268] using wordTrace_append hprefix tailTrace_3364268
  have hstable : (prefixWord ++ tailWord_3364268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364268).length < 2 ^ (prefixWord ++ tailWord_3364268).sum := by decide
  have hdescent : baseEnd_3364268 < baseStart_3364268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364288 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2]
def baseStart_3364288 : Nat := 118140960795 + 3364288 * 2 ^ 59
def prefixEnd_3364288 : Nat := 4983230072969 + 3 ^ 40 * 3364288 * 2
def baseEnd_3364288 : Nat := 1727496804153438441427927

theorem tailTrace_3364288 : CollatzResearch.WordTrace tailWord_3364288 prefixEnd_3364288 1727496804153438441427927 := by
  unfold tailWord_3364288
  simp only [CollatzResearch.WordTrace]
  refine ⟨61352832017883312745642759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81803776023844416994190345 61352832017883312745642759)
  ·
    refine ⟨92029248026824969118464139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61352832017883312745642759 92029248026824969118464139)
    ·
      refine ⟨138043872040237453677696209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92029248026824969118464139 138043872040237453677696209)
      ·
        refine ⟨103532904030178090258272157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138043872040237453677696209 103532904030178090258272157)
        ·
          refine ⟨38824839011316783846852059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103532904030178090258272157 38824839011316783846852059)
          ·
            refine ⟨58237258516975175770278089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38824839011316783846852059 58237258516975175770278089)
            ·
              refine ⟨43677943887731381827708567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58237258516975175770278089 43677943887731381827708567)
              ·
                refine ⟨65516915831597072741562851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43677943887731381827708567 65516915831597072741562851)
                ·
                  refine ⟨98275373747395609112344277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65516915831597072741562851 98275373747395609112344277)
                  ·
                    refine ⟨2303329072204584588570569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 98275373747395609112344277 2303329072204584588570569)
                    ·
                      refine ⟨1727496804153438441427927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303329072204584588570569 1727496804153438441427927)
                      ·
                        rfl

theorem cell23_3364288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_3364288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364288 prefixEnd_3364288 := by exact prefixLift 3364288
  have htrace : WordTrace (prefixWord ++ tailWord_3364288) baseStart_3364288 baseEnd_3364288 := by
    simpa [prefixWord, tailWord_3364288, baseEnd_3364288] using wordTrace_append hprefix tailTrace_3364288
  have hstable : (prefixWord ++ tailWord_3364288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364288).length < 2 ^ (prefixWord ++ tailWord_3364288).sum := by decide
  have hdescent : baseEnd_3364288 < baseStart_3364288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364290 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_3364290 : Nat := 118140960795 + 3364290 * 2 ^ 59
def prefixEnd_3364290 : Nat := 4983230072969 + 3 ^ 40 * 3364290 * 2
def baseEnd_3364290 : Nat := 1727497831114747433602919

theorem tailTrace_3364290 : CollatzResearch.WordTrace tailWord_3364290 prefixEnd_3364290 1727497831114747433602919 := by
  unfold tailWord_3364290
  simp only [CollatzResearch.WordTrace]
  refine ⟨30676434245439844958214581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81803824654506253221905549 30676434245439844958214581)
  ·
    refine ⟨2875915710509985464832617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30676434245439844958214581 2875915710509985464832617)
    ·
      refine ⟨2156936782882489098624463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2875915710509985464832617 2156936782882489098624463)
      ·
        refine ⟨3235405174323733647936695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156936782882489098624463 3235405174323733647936695)
        ·
          refine ⟨4853107761485600471905043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235405174323733647936695 4853107761485600471905043)
          ·
            refine ⟨7279661642228400707857565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853107761485600471905043 7279661642228400707857565)
            ·
              refine ⟨2729873115835650265446587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7279661642228400707857565 2729873115835650265446587)
              ·
                refine ⟨4094809673753475398169881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729873115835650265446587 4094809673753475398169881)
                ·
                  refine ⟨3071107255315106548627411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4094809673753475398169881 3071107255315106548627411)
                  ·
                    refine ⟨4606660882972659822941117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3071107255315106548627411 4606660882972659822941117)
                    ·
                      refine ⟨1727497831114747433602919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4606660882972659822941117 1727497831114747433602919)
                      ·
                        rfl

theorem cell23_3364290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_3364290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364290 prefixEnd_3364290 := by exact prefixLift 3364290
  have htrace : WordTrace (prefixWord ++ tailWord_3364290) baseStart_3364290 baseEnd_3364290 := by
    simpa [prefixWord, tailWord_3364290, baseEnd_3364290] using wordTrace_append hprefix tailTrace_3364290
  have hstable : (prefixWord ++ tailWord_3364290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364290).length < 2 ^ (prefixWord ++ tailWord_3364290).sum := by decide
  have hdescent : baseEnd_3364290 < baseStart_3364290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364291 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5]
def baseStart_3364291 : Nat := 118140960795 + 3364291 * 2 ^ 59
def prefixEnd_3364291 : Nat := 4983230072969 + 3 ^ 40 * 3364291 * 2
def baseEnd_3364291 : Nat := 1727498344595401929690413

theorem tailTrace_3364291 : CollatzResearch.WordTrace tailWord_3364291 prefixEnd_3364291 1727498344595401929690413 := by
  unfold tailWord_3364291
  simp only [CollatzResearch.WordTrace]
  refine ⟨122705773454755757003644727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81803848969837171335763151 122705773454755757003644727)
  ·
    refine ⟨184058660182133635505467091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122705773454755757003644727 184058660182133635505467091)
    ·
      refine ⟨276087990273200453258200637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184058660182133635505467091 276087990273200453258200637)
      ·
        refine ⟨103532996352450169971825239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276087990273200453258200637 103532996352450169971825239)
        ·
          refine ⟨155299494528675254957737859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103532996352450169971825239 155299494528675254957737859)
          ·
            refine ⟨232949241793012882436606789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155299494528675254957737859 232949241793012882436606789)
            ·
              refine ⟨43677982836189915456863773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232949241793012882436606789 43677982836189915456863773)
              ·
                refine ⟨16379243563571218296323915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43677982836189915456863773 16379243563571218296323915)
                ·
                  refine ⟨24568865345356827444485873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16379243563571218296323915 24568865345356827444485873)
                  ·
                    refine ⟨18426649009017620583364405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24568865345356827444485873 18426649009017620583364405)
                    ·
                      refine ⟨1727498344595401929690413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18426649009017620583364405 1727498344595401929690413)
                      ·
                        rfl

theorem cell23_3364291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_3364291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364291 prefixEnd_3364291 := by exact prefixLift 3364291
  have htrace : WordTrace (prefixWord ++ tailWord_3364291) baseStart_3364291 baseEnd_3364291 := by
    simpa [prefixWord, tailWord_3364291, baseEnd_3364291] using wordTrace_append hprefix tailTrace_3364291
  have hstable : (prefixWord ++ tailWord_3364291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364291).length < 2 ^ (prefixWord ++ tailWord_3364291).sum := by decide
  have hdescent : baseEnd_3364291 < baseStart_3364291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364331 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6]
def baseStart_3364331 : Nat := 118140960795 + 3364331 * 2 ^ 59
def prefixEnd_3364331 : Nat := 4983230072969 + 3 ^ 40 * 3364331 * 2
def baseEnd_3364331 : Nat := 1727518883821581773190229

theorem tailTrace_3364331 : CollatzResearch.WordTrace tailWord_3364331 prefixEnd_3364331 1727518883821581773190229 := by
  unfold tailWord_3364331
  simp only [CollatzResearch.WordTrace]
  refine ⟨122707232374610843835100847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81804821583073895890067231 122707232374610843835100847)
  ·
    refine ⟨184060848561916265752651271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122707232374610843835100847 184060848561916265752651271)
    ·
      refine ⟨276091272842874398628976907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184060848561916265752651271 276091272842874398628976907)
      ·
        refine ⟨414136909264311597943465361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276091272842874398628976907 414136909264311597943465361)
        ·
          refine ⟨310602681948233698457599021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414136909264311597943465361 310602681948233698457599021)
          ·
            refine ⟨116476005730587636921599633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310602681948233698457599021 116476005730587636921599633)
            ·
              refine ⟨87357004297940727691199725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116476005730587636921599633 87357004297940727691199725)
              ·
                refine ⟨32758876611727772884199897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87357004297940727691199725 32758876611727772884199897)
                ·
                  refine ⟨24569157458795829663149923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32758876611727772884199897 24569157458795829663149923)
                  ·
                    refine ⟨36853736188193744494724885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24569157458795829663149923 36853736188193744494724885)
                    ·
                      refine ⟨1727518883821581773190229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36853736188193744494724885 1727518883821581773190229)
                      ·
                        rfl

theorem cell23_3364331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_3364331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364331 prefixEnd_3364331 := by exact prefixLift 3364331
  have htrace : WordTrace (prefixWord ++ tailWord_3364331) baseStart_3364331 baseEnd_3364331 := by
    simpa [prefixWord, tailWord_3364331, baseEnd_3364331] using wordTrace_append hprefix tailTrace_3364331
  have hstable : (prefixWord ++ tailWord_3364331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364331).length < 2 ^ (prefixWord ++ tailWord_3364331).sum := by decide
  have hdescent : baseEnd_3364331 < baseStart_3364331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364392 : List Nat := [2, 1, 5, 2, 2, 1, 2, 2, 6]
def baseStart_3364392 : Nat := 118140960795 + 3364392 * 2 ^ 59
def prefixEnd_3364392 : Nat := 4983230072969 + 3 ^ 40 * 3364392 * 2
def baseEnd_3364392 : Nat := 191950022904611781614161

theorem tailTrace_3364392 : CollatzResearch.WordTrace tailWord_3364392 prefixEnd_3364392 191950022904611781614161 := by
  unfold tailWord_3364392
  simp only [CollatzResearch.WordTrace]
  refine ⟨61354728613694925626535715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81806304818259900835380953 61354728613694925626535715)
  ·
    refine ⟨92032092920542388439803573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61354728613694925626535715 92032092920542388439803573)
    ·
      refine ⟨8628008711300848916231585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92032092920542388439803573 8628008711300848916231585)
      ·
        refine ⟨6471006533475636687173689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8628008711300848916231585 6471006533475636687173689)
        ·
          refine ⟨4853254900106727515380267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6471006533475636687173689 4853254900106727515380267)
          ·
            refine ⟨7279882350160091273070401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853254900106727515380267 7279882350160091273070401)
            ·
              refine ⟨5459911762620068454802801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7279882350160091273070401 5459911762620068454802801)
              ·
                refine ⟨4094933821965051341102101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5459911762620068454802801 4094933821965051341102101)
                ·
                  refine ⟨191950022904611781614161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4094933821965051341102101 191950022904611781614161)
                  ·
                    rfl

theorem cell23_3364392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_3364392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364392 prefixEnd_3364392 := by exact prefixLift 3364392
  have htrace : WordTrace (prefixWord ++ tailWord_3364392) baseStart_3364392 baseEnd_3364392 := by
    simpa [prefixWord, tailWord_3364392, baseEnd_3364392] using wordTrace_append hprefix tailTrace_3364392
  have hstable : (prefixWord ++ tailWord_3364392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364392).length < 2 ^ (prefixWord ++ tailWord_3364392).sum := by decide
  have hdescent : baseEnd_3364392 < baseStart_3364392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364429 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_3364429 : Nat := 118140960795 + 3364429 * 2 ^ 59
def prefixEnd_3364429 : Nat := 4983230072969 + 3 ^ 40 * 3364429 * 2
def baseEnd_3364429 : Nat := 1727569204925722389764779

theorem tailTrace_3364429 : CollatzResearch.WordTrace tailWord_3364429 prefixEnd_3364429 1727569204925722389764779 := by
  unfold tailWord_3364429
  simp only [CollatzResearch.WordTrace]
  refine ⟨122710806728255806572168341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81807204485503871048112227 122710806728255806572168341)
  ·
    refine ⟨5752069065386990933070391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122710806728255806572168341 5752069065386990933070391)
    ·
      refine ⟨8628103598080486399605587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752069065386990933070391 8628103598080486399605587)
      ·
        refine ⟨12942155397120729599408381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628103598080486399605587 12942155397120729599408381)
        ·
          refine ⟨4853308273920273599778143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12942155397120729599408381 4853308273920273599778143)
          ·
            refine ⟨7279962410880410399667215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853308273920273599778143 7279962410880410399667215)
            ·
              refine ⟨10919943616320615599500823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7279962410880410399667215 10919943616320615599500823)
              ·
                refine ⟨16379915424480923399251235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10919943616320615599500823 16379915424480923399251235)
                ·
                  refine ⟨24569873136721385098876853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16379915424480923399251235 24569873136721385098876853)
                  ·
                    refine ⟨2303425606567629853019705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24569873136721385098876853 2303425606567629853019705)
                    ·
                      refine ⟨1727569204925722389764779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303425606567629853019705 1727569204925722389764779)
                      ·
                        rfl

theorem cell23_3364429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_3364429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364429 prefixEnd_3364429 := by exact prefixLift 3364429
  have htrace : WordTrace (prefixWord ++ tailWord_3364429) baseStart_3364429 baseEnd_3364429 := by
    simpa [prefixWord, tailWord_3364429, baseEnd_3364429] using wordTrace_append hprefix tailTrace_3364429
  have hstable : (prefixWord ++ tailWord_3364429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364429).length < 2 ^ (prefixWord ++ tailWord_3364429).sum := by decide
  have hdescent : baseEnd_3364429 < baseStart_3364429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364452 : List Nat := [2, 3, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_3364452 : Nat := 118140960795 + 3364452 * 2 ^ 59
def prefixEnd_3364452 : Nat := 4983230072969 + 3 ^ 40 * 3364452 * 2
def baseEnd_3364452 : Nat := 575860338326925266592391

theorem tailTrace_3364452 : CollatzResearch.WordTrace tailWord_3364452 prefixEnd_3364452 575860338326925266592391 := by
  unfold tailWord_3364452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61355822803586240750127805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81807763738114987666837073 61355822803586240750127805)
  ·
    refine ⟨23008433551344840281297927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61355822803586240750127805 23008433551344840281297927)
    ·
      refine ⟨34512650327017260421946891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23008433551344840281297927 34512650327017260421946891)
      ·
        refine ⟨51768975490525890632920337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34512650327017260421946891 51768975490525890632920337)
        ·
          refine ⟨38826731617894417974690253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51768975490525890632920337 38826731617894417974690253)
          ·
            refine ⟨14560024356710406740508845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38826731617894417974690253 14560024356710406740508845)
            ·
              refine ⟨5460009133766402527690817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14560024356710406740508845 5460009133766402527690817)
              ·
                refine ⟨4095006850324801895768113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5460009133766402527690817 4095006850324801895768113)
                ·
                  refine ⟨3071255137743601421826085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095006850324801895768113 3071255137743601421826085)
                  ·
                    refine ⟨575860338326925266592391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071255137743601421826085 575860338326925266592391)
                    ·
                      rfl

theorem cell23_3364452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_3364452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364452 prefixEnd_3364452 := by exact prefixLift 3364452
  have htrace : WordTrace (prefixWord ++ tailWord_3364452) baseStart_3364452 baseEnd_3364452 := by
    simpa [prefixWord, tailWord_3364452, baseEnd_3364452] using wordTrace_append hprefix tailTrace_3364452
  have hstable : (prefixWord ++ tailWord_3364452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364452).length < 2 ^ (prefixWord ++ tailWord_3364452).sum := by decide
  have hdescent : baseEnd_3364452 < baseStart_3364452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364462 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5]
def baseStart_3364462 : Nat := 118140960795 + 3364462 * 2 ^ 59
def prefixEnd_3364462 : Nat := 4983230072969 + 3 ^ 40 * 3364462 * 2
def baseEnd_3364462 : Nat := 1727586149787320760652127

theorem tailTrace_3364462 : CollatzResearch.WordTrace tailWord_3364462 prefixEnd_3364462 1727586149787320760652127 := by
  unfold tailWord_3364462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339001292142031651014955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81808006891424168805413093 15339001292142031651014955)
  ·
    refine ⟨23008501938213047476522433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15339001292142031651014955 23008501938213047476522433)
    ·
      refine ⟨17256376453659785607391825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23008501938213047476522433 17256376453659785607391825)
      ·
        refine ⟨12942282340244839205543869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17256376453659785607391825 12942282340244839205543869)
        ·
          refine ⟨4853355877591814702078951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12942282340244839205543869 4853355877591814702078951)
          ·
            refine ⟨7280033816387722053118427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853355877591814702078951 7280033816387722053118427)
            ·
              refine ⟨10920050724581583079677641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7280033816387722053118427 10920050724581583079677641)
              ·
                refine ⟨8190038043436187309758231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10920050724581583079677641 8190038043436187309758231)
                ·
                  refine ⟨12285057065154280964637347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190038043436187309758231 12285057065154280964637347)
                  ·
                    refine ⟨18427585597731421446956021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12285057065154280964637347 18427585597731421446956021)
                    ·
                      refine ⟨1727586149787320760652127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18427585597731421446956021 1727586149787320760652127)
                      ·
                        rfl

theorem cell23_3364462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_3364462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364462 prefixEnd_3364462 := by exact prefixLift 3364462
  have htrace : WordTrace (prefixWord ++ tailWord_3364462) baseStart_3364462 baseEnd_3364462 := by
    simpa [prefixWord, tailWord_3364462, baseEnd_3364462] using wordTrace_append hprefix tailTrace_3364462
  have hstable : (prefixWord ++ tailWord_3364462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364462).length < 2 ^ (prefixWord ++ tailWord_3364462).sum := by decide
  have hdescent : baseEnd_3364462 < baseStart_3364462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364510 : List Nat := [4, 3, 1, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_3364510 : Nat := 118140960795 + 3364510 * 2 ^ 59
def prefixEnd_3364510 : Nat := 4983230072969 + 3 ^ 40 * 3364510 * 2
def baseEnd_3364510 : Nat := 1727610796858736572851907

theorem tailTrace_3364510 : CollatzResearch.WordTrace tailWord_3364510 prefixEnd_3364510 1727610796858736572851907 := by
  unfold tailWord_3364510
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339220130120294675733373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81809174027308238270577989 15339220130120294675733373)
  ·
    refine ⟨5752207548795110503400015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15339220130120294675733373 5752207548795110503400015)
    ·
      refine ⟨8628311323192665755100023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5752207548795110503400015 8628311323192665755100023)
      ·
        refine ⟨12942466984788998632650035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628311323192665755100023 12942466984788998632650035)
        ·
          refine ⟨19413700477183497948975053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12942466984788998632650035 19413700477183497948975053)
          ·
            refine ⟨7280137678943811730865645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19413700477183497948975053 7280137678943811730865645)
            ·
              refine ⟨2730051629603929399074617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7280137678943811730865645 2730051629603929399074617)
              ·
                refine ⟨2047538722202947049305963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730051629603929399074617 2047538722202947049305963)
                ·
                  refine ⟨3071308083304420573958945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047538722202947049305963 3071308083304420573958945)
                  ·
                    refine ⟨2303481062478315430469209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3071308083304420573958945 2303481062478315430469209)
                    ·
                      refine ⟨1727610796858736572851907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303481062478315430469209 1727610796858736572851907)
                      ·
                        rfl

theorem cell23_3364510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_3364510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364510 prefixEnd_3364510 := by exact prefixLift 3364510
  have htrace : WordTrace (prefixWord ++ tailWord_3364510) baseStart_3364510 baseEnd_3364510 := by
    simpa [prefixWord, tailWord_3364510, baseEnd_3364510] using wordTrace_append hprefix tailTrace_3364510
  have hstable : (prefixWord ++ tailWord_3364510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364510).length < 2 ^ (prefixWord ++ tailWord_3364510).sum := by decide
  have hdescent : baseEnd_3364510 < baseStart_3364510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364520 : List Nat := [2, 1, 7, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3364520 : Nat := 118140960795 + 3364520 * 2 ^ 59
def prefixEnd_3364520 : Nat := 4983230072969 + 3 ^ 40 * 3364520 * 2
def baseEnd_3364520 : Nat := 575871977221760511242287

theorem tailTrace_3364520 : CollatzResearch.WordTrace tailWord_3364520 prefixEnd_3364520 575871977221760511242287 := by
  unfold tailWord_3364520
  simp only [CollatzResearch.WordTrace]
  refine ⟨61357062885463064556865507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81809417180617419409154009 61357062885463064556865507)
  ·
    refine ⟨92035594328194596835298261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61357062885463064556865507 92035594328194596835298261)
    ·
      refine ⟨2157084242067060863327303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 92035594328194596835298261 2157084242067060863327303)
      ·
        refine ⟨3235626363100591294990955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2157084242067060863327303 3235626363100591294990955)
        ·
          refine ⟨4853439544650886942486433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235626363100591294990955 4853439544650886942486433)
          ·
            refine ⟨3640079658488165206864825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4853439544650886942486433 3640079658488165206864825)
            ·
              refine ⟨2730059743866123905148619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640079658488165206864825 2730059743866123905148619)
              ·
                refine ⟨4095089615799185857722929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730059743866123905148619 4095089615799185857722929)
                ·
                  refine ⟨3071317211849389393292197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095089615799185857722929 3071317211849389393292197)
                  ·
                    refine ⟨575871977221760511242287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071317211849389393292197 575871977221760511242287)
                    ·
                      rfl

theorem cell23_3364520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3364520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364520 prefixEnd_3364520 := by exact prefixLift 3364520
  have htrace : WordTrace (prefixWord ++ tailWord_3364520) baseStart_3364520 baseEnd_3364520 := by
    simpa [prefixWord, tailWord_3364520, baseEnd_3364520] using wordTrace_append hprefix tailTrace_3364520
  have hstable : (prefixWord ++ tailWord_3364520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364520).length < 2 ^ (prefixWord ++ tailWord_3364520).sum := by decide
  have hdescent : baseEnd_3364520 < baseStart_3364520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364525 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3364525 : Nat := 118140960795 + 3364525 * 2 ^ 59
def prefixEnd_3364525 : Nat := 4983230072969 + 3 ^ 40 * 3364525 * 2
def baseEnd_3364525 : Nat := 575872833022851338054779

theorem tailTrace_3364525 : CollatzResearch.WordTrace tailWord_3364525 prefixEnd_3364525 575872833022851338054779 := by
  unfold tailWord_3364525
  simp only [CollatzResearch.WordTrace]
  refine ⟨122714308135908014967663029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81809538757272009978442019 122714308135908014967663029)
  ·
    refine ⟨11504466387741376403218409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122714308135908014967663029 11504466387741376403218409)
    ·
      refine ⟨8628349790806032302413807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11504466387741376403218409 8628349790806032302413807)
      ·
        refine ⟨12942524686209048453620711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628349790806032302413807 12942524686209048453620711)
        ·
          refine ⟨19413787029313572680431067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12942524686209048453620711 19413787029313572680431067)
          ·
            refine ⟨29120680543970359020646601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19413787029313572680431067 29120680543970359020646601)
            ·
              refine ⟨21840510407977769265484951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29120680543970359020646601 21840510407977769265484951)
              ·
                refine ⟨32760765611966653898227427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21840510407977769265484951 32760765611966653898227427)
                ·
                  refine ⟨49141148417949980847341141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32760765611966653898227427 49141148417949980847341141)
                  ·
                    refine ⟨575872833022851338054779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49141148417949980847341141 575872833022851338054779)
                    ·
                      rfl

theorem cell23_3364525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3364525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364525 prefixEnd_3364525 := by exact prefixLift 3364525
  have htrace : WordTrace (prefixWord ++ tailWord_3364525) baseStart_3364525 baseEnd_3364525 := by
    simpa [prefixWord, tailWord_3364525, baseEnd_3364525] using wordTrace_append hprefix tailTrace_3364525
  have hstable : (prefixWord ++ tailWord_3364525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364525).length < 2 ^ (prefixWord ++ tailWord_3364525).sum := by decide
  have hdescent : baseEnd_3364525 < baseStart_3364525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364535 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5]
def baseStart_3364535 : Nat := 118140960795 + 3364535 * 2 ^ 59
def prefixEnd_3364535 : Nat := 4983230072969 + 3 ^ 40 * 3364535 * 2
def baseEnd_3364535 : Nat := 1727623633875098975039291

theorem tailTrace_3364535 : CollatzResearch.WordTrace tailWord_3364535 prefixEnd_3364535 1727623633875098975039291 := by
  unfold tailWord_3364535
  simp only [CollatzResearch.WordTrace]
  refine ⟨122714672865871786675527059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81809781910581191117018039 122714672865871786675527059)
  ·
    refine ⟨184072009298807680013290589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122714672865871786675527059 184072009298807680013290589)
    ·
      refine ⟨69027003487052880004983971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184072009298807680013290589 69027003487052880004983971)
      ·
        refine ⟨103540505230579320007475957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69027003487052880004983971 103540505230579320007475957)
        ·
          refine ⟨9706922365366811250700871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103540505230579320007475957 9706922365366811250700871)
          ·
            refine ⟨14560383548050216876051307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9706922365366811250700871 14560383548050216876051307)
            ·
              refine ⟨21840575322075325314076961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14560383548050216876051307 21840575322075325314076961)
              ·
                refine ⟨16380431491556493985557721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21840575322075325314076961 16380431491556493985557721)
                ·
                  refine ⟨12285323618667370489168291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16380431491556493985557721 12285323618667370489168291)
                  ·
                    refine ⟨18427985428001055733752437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12285323618667370489168291 18427985428001055733752437)
                    ·
                      refine ⟨1727623633875098975039291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18427985428001055733752437 1727623633875098975039291)
                      ·
                        rfl

theorem cell23_3364535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_3364535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364535 prefixEnd_3364535 := by exact prefixLift 3364535
  have htrace : WordTrace (prefixWord ++ tailWord_3364535) baseStart_3364535 baseEnd_3364535 := by
    simpa [prefixWord, tailWord_3364535, baseEnd_3364535] using wordTrace_append hprefix tailTrace_3364535
  have hstable : (prefixWord ++ tailWord_3364535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364535).length < 2 ^ (prefixWord ++ tailWord_3364535).sum := by decide
  have hdescent : baseEnd_3364535 < baseStart_3364535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364606 : List Nat := [4, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3364606 : Nat := 118140960795 + 3364606 * 2 ^ 59
def prefixEnd_3364606 : Nat := 4983230072969 + 3 ^ 40 * 3364606 * 2
def baseEnd_3364606 : Nat := 191962232333507577472385

theorem tailTrace_3364606 : CollatzResearch.WordTrace tailWord_3364606 prefixEnd_3364606 191962232333507577472385 := by
  unfold tailWord_3364606
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339657806076820725170209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81811508299076377200907781 15339657806076820725170209)
  ·
    refine ⟨11504743354557615543877657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15339657806076820725170209 11504743354557615543877657)
    ·
      refine ⟨8628557515918211657908243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11504743354557615543877657 8628557515918211657908243)
      ·
        refine ⟨12942836273877317486862365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628557515918211657908243 12942836273877317486862365)
        ·
          refine ⟨4853563602703994057573387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12942836273877317486862365 4853563602703994057573387)
          ·
            refine ⟨7280345404055991086360081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853563602703994057573387 7280345404055991086360081)
            ·
              refine ⟨5460259053041993314770061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280345404055991086360081 5460259053041993314770061)
              ·
                refine ⟨2047597144890747493038773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5460259053041993314770061 2047597144890747493038773)
                ·
                  refine ⟨191962232333507577472385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2047597144890747493038773 191962232333507577472385)
                  ·
                    rfl

theorem cell23_3364606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3364606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364606 prefixEnd_3364606 := by exact prefixLift 3364606
  have htrace : WordTrace (prefixWord ++ tailWord_3364606) baseStart_3364606 baseEnd_3364606 := by
    simpa [prefixWord, tailWord_3364606, baseEnd_3364606] using wordTrace_append hprefix tailTrace_3364606
  have hstable : (prefixWord ++ tailWord_3364606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364606).length < 2 ^ (prefixWord ++ tailWord_3364606).sum := by decide
  have hdescent : baseEnd_3364606 < baseStart_3364606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364622 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_3364622 : Nat := 118140960795 + 3364622 * 2 ^ 59
def prefixEnd_3364622 : Nat := 4983230072969 + 3 ^ 40 * 3364622 * 2
def baseEnd_3364622 : Nat := 1727668306692040134651391

theorem tailTrace_3364622 : CollatzResearch.WordTrace tailWord_3364622 prefixEnd_3364622 1727668306692040134651391 := by
  unfold tailWord_3364622
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339730752069575066743015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81811897344371067022629413 15339730752069575066743015)
  ·
    refine ⟨23009596128104362600114523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15339730752069575066743015 23009596128104362600114523)
    ·
      refine ⟨34514394192156543900171785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23009596128104362600114523 34514394192156543900171785)
      ·
        refine ⟨25885795644117407925128839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34514394192156543900171785 25885795644117407925128839)
        ·
          refine ⟨38828693466176111887693259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25885795644117407925128839 38828693466176111887693259)
          ·
            refine ⟨58243040199264167831539889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38828693466176111887693259 58243040199264167831539889)
            ·
              refine ⟨43682280149448125873654917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58243040199264167831539889 43682280149448125873654917)
              ·
                refine ⟨8190427528021523601310297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43682280149448125873654917 8190427528021523601310297)
                ·
                  refine ⟨6142820646016142700982723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8190427528021523601310297 6142820646016142700982723)
                  ·
                    refine ⟨9214230969024214051474085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6142820646016142700982723 9214230969024214051474085)
                    ·
                      refine ⟨1727668306692040134651391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9214230969024214051474085 1727668306692040134651391)
                      ·
                        rfl

theorem cell23_3364622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_3364622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364622 prefixEnd_3364622 := by exact prefixLift 3364622
  have htrace : WordTrace (prefixWord ++ tailWord_3364622) baseStart_3364622 baseEnd_3364622 := by
    simpa [prefixWord, tailWord_3364622, baseEnd_3364622] using wordTrace_append hprefix tailTrace_3364622
  have hstable : (prefixWord ++ tailWord_3364622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364622).length < 2 ^ (prefixWord ++ tailWord_3364622).sum := by decide
  have hdescent : baseEnd_3364622 < baseStart_3364622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364632 : List Nat := [2, 1, 2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_3364632 : Nat := 118140960795 + 3364632 * 2 ^ 59
def prefixEnd_3364632 : Nat := 4983230072969 + 3 ^ 40 * 3364632 * 2
def baseEnd_3364632 : Nat := 575891147166195031842115

theorem tailTrace_3364632 : CollatzResearch.WordTrace tailWord_3364632 prefixEnd_3364632 575891147166195031842115 := by
  unfold tailWord_3364632
  simp only [CollatzResearch.WordTrace]
  refine ⟨61359105373260186120904075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81812140497680248161205433 61359105373260186120904075)
  ·
    refine ⟨92038658059890279181356113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61359105373260186120904075 92038658059890279181356113)
    ·
      refine ⟨69028993544917709386017085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92038658059890279181356113 69028993544917709386017085)
      ·
        refine ⟨25885872579344141019756407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69028993544917709386017085 25885872579344141019756407)
        ·
          refine ⟨38828808869016211529634611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25885872579344141019756407 38828808869016211529634611)
          ·
            refine ⟨58243213303524317294451917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38828808869016211529634611 58243213303524317294451917)
            ·
              refine ⟨21841204988821618985419469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58243213303524317294451917 21841204988821618985419469)
              ·
                refine ⟨8190451870808107119532301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21841204988821618985419469 8190451870808107119532301)
                ·
                  refine ⟨3071419451553040169824613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8190451870808107119532301 3071419451553040169824613)
                  ·
                    refine ⟨575891147166195031842115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071419451553040169824613 575891147166195031842115)
                    ·
                      rfl

theorem cell23_3364632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_3364632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364632 prefixEnd_3364632 := by exact prefixLift 3364632
  have htrace : WordTrace (prefixWord ++ tailWord_3364632) baseStart_3364632 baseEnd_3364632 := by
    simpa [prefixWord, tailWord_3364632, baseEnd_3364632] using wordTrace_append hprefix tailTrace_3364632
  have hstable : (prefixWord ++ tailWord_3364632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364632).length < 2 ^ (prefixWord ++ tailWord_3364632).sum := by decide
  have hdescent : baseEnd_3364632 < baseStart_3364632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364642 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 3, 4, 3]
def baseStart_3364642 : Nat := 118140960795 + 3364642 * 2 ^ 59
def prefixEnd_3364642 : Nat := 4983230072969 + 3 ^ 40 * 3364642 * 2
def baseEnd_3364642 : Nat := 1727678576305130056401299

theorem tailTrace_3364642 : CollatzResearch.WordTrace tailWord_3364642 prefixEnd_3364642 1727678576305130056401299 := by
  unfold tailWord_3364642
  simp only [CollatzResearch.WordTrace]
  refine ⟨30679643869121035987418045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81812383650989429299781453 30679643869121035987418045)
  ·
    refine ⟨11504866450920388495281767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30679643869121035987418045 11504866450920388495281767)
    ·
      refine ⟨17257299676380582742922651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11504866450920388495281767 17257299676380582742922651)
      ·
        refine ⟨25885949514570874114383977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17257299676380582742922651 25885949514570874114383977)
        ·
          refine ⟨19414462135928155585787983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25885949514570874114383977 19414462135928155585787983)
          ·
            refine ⟨29121693203892233378681975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19414462135928155585787983 29121693203892233378681975)
            ·
              refine ⟨43682539805838350068022963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29121693203892233378681975 43682539805838350068022963)
              ·
                refine ⟨65523809708757525102034445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43682539805838350068022963 65523809708757525102034445)
                ·
                  refine ⟨24571428640784071913262917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65523809708757525102034445 24571428640784071913262917)
                  ·
                    refine ⟨4607142870147013483736797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24571428640784071913262917 4607142870147013483736797)
                    ·
                      refine ⟨1727678576305130056401299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4607142870147013483736797 1727678576305130056401299)
                      ·
                        rfl

theorem cell23_3364642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_3364642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364642 prefixEnd_3364642 := by exact prefixLift 3364642
  have htrace : WordTrace (prefixWord ++ tailWord_3364642) baseStart_3364642 baseEnd_3364642 := by
    simpa [prefixWord, tailWord_3364642, baseEnd_3364642] using wordTrace_append hprefix tailTrace_3364642
  have hstable : (prefixWord ++ tailWord_3364642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364642).length < 2 ^ (prefixWord ++ tailWord_3364642).sum := by decide
  have hdescent : baseEnd_3364642 < baseStart_3364642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364666 : List Nat := [3, 1, 1, 1, 5, 1, 3, 3, 1, 4]
def baseStart_3364666 : Nat := 118140960795 + 3364666 * 2 ^ 59
def prefixEnd_3364666 : Nat := 4983230072969 + 3 ^ 40 * 3364666 * 2
def baseEnd_3364666 : Nat := 575896966613612654167063

theorem tailTrace_3364666 : CollatzResearch.WordTrace tailWord_3364666 prefixEnd_3364666 575896966613612654167063 := by
  unfold tailWord_3364666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30679862707099299012136463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81812967218931464032363901 30679862707099299012136463)
  ·
    refine ⟨46019794060648948518204695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30679862707099299012136463 46019794060648948518204695)
    ·
      refine ⟨69029691090973422777307043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46019794060648948518204695 69029691090973422777307043)
      ·
        refine ⟨103544536636460134165960565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69029691090973422777307043 103544536636460134165960565)
        ·
          refine ⟨9707300309668137578058803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103544536636460134165960565 9707300309668137578058803)
          ·
            refine ⟨14560950464502206367088205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707300309668137578058803 14560950464502206367088205)
            ·
              refine ⟨5460356424188327387658077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14560950464502206367088205 5460356424188327387658077)
              ·
                refine ⟨2047633659070622770371779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5460356424188327387658077 2047633659070622770371779)
                ·
                  refine ⟨3071450488605934155557669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047633659070622770371779 3071450488605934155557669)
                  ·
                    refine ⟨575896966613612654167063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071450488605934155557669 575896966613612654167063)
                    ·
                      rfl

theorem cell23_3364666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 3, 1, 4].length) (baseStart_3364666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364666 prefixEnd_3364666 := by exact prefixLift 3364666
  have htrace : WordTrace (prefixWord ++ tailWord_3364666) baseStart_3364666 baseEnd_3364666 := by
    simpa [prefixWord, tailWord_3364666, baseEnd_3364666] using wordTrace_append hprefix tailTrace_3364666
  have hstable : (prefixWord ++ tailWord_3364666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364666).length < 2 ^ (prefixWord ++ tailWord_3364666).sum := by decide
  have hdescent : baseEnd_3364666 < baseStart_3364666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364716 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_3364716 : Nat := 118140960795 + 3364716 * 2 ^ 59
def prefixEnd_3364716 : Nat := 4983230072969 + 3 ^ 40 * 3364716 * 2
def baseEnd_3364716 : Nat := 1727716573873562766875959

theorem tailTrace_3364716 : CollatzResearch.WordTrace tailWord_3364716 prefixEnd_3364716 1727716573873562766875959 := by
  unfold tailWord_3364716
  simp only [CollatzResearch.WordTrace]
  refine ⟨61360637239108027293933001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81814182985477369725244001 61360637239108027293933001)
  ·
    refine ⟨46020477929331020470449751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61360637239108027293933001 46020477929331020470449751)
    ·
      refine ⟨69030716893996530705674627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46020477929331020470449751 69030716893996530705674627)
      ·
        refine ⟨103546075340994796058511941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69030716893996530705674627 103546075340994796058511941)
        ·
          refine ⟨19414889126436524260970989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103546075340994796058511941 19414889126436524260970989)
          ·
            refine ⟨7280583422413696597864121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19414889126436524260970989 7280583422413696597864121)
            ·
              refine ⟨5460437566810272448398091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280583422413696597864121 5460437566810272448398091)
              ·
                refine ⟨8190656350215408672597137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460437566810272448398091 8190656350215408672597137)
                ·
                  refine ⟨6142992262661556504447853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8190656350215408672597137 6142992262661556504447853)
                  ·
                    refine ⟨2303622098498083689167945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6142992262661556504447853 2303622098498083689167945)
                    ·
                      refine ⟨1727716573873562766875959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303622098498083689167945 1727716573873562766875959)
                      ·
                        rfl

theorem cell23_3364716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_3364716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364716 prefixEnd_3364716 := by exact prefixLift 3364716
  have htrace : WordTrace (prefixWord ++ tailWord_3364716) baseStart_3364716 baseEnd_3364716 := by
    simpa [prefixWord, tailWord_3364716, baseEnd_3364716] using wordTrace_append hprefix tailTrace_3364716
  have hstable : (prefixWord ++ tailWord_3364716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364716).length < 2 ^ (prefixWord ++ tailWord_3364716).sum := by decide
  have hdescent : baseEnd_3364716 < baseStart_3364716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364739 : List Nat := [1, 1, 1, 3, 4, 2, 1, 4, 2, 4]
def baseStart_3364739 : Nat := 118140960795 + 3364739 * 2 ^ 59
def prefixEnd_3364739 : Nat := 4983230072969 + 3 ^ 40 * 3364739 * 2
def baseEnd_3364739 : Nat := 575909461309538725629451

theorem tailTrace_3364739 : CollatzResearch.WordTrace tailWord_3364739 prefixEnd_3364739 575909461309538725629451 := by
  unfold tailWord_3364739
  simp only [CollatzResearch.WordTrace]
  refine ⟨122722113357132729515953271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81814742238088486343968847 122722113357132729515953271)
  ·
    refine ⟨184083170035699094273929907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122722113357132729515953271 184083170035699094273929907)
    ·
      refine ⟨276124755053548641410894861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184083170035699094273929907 276124755053548641410894861)
      ·
        refine ⟨103546783145080740529085573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276124755053548641410894861 103546783145080740529085573)
        ·
          refine ⟨19415021839702638849203545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103546783145080740529085573 19415021839702638849203545)
          ·
            refine ⟨14561266379776979136902659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19415021839702638849203545 14561266379776979136902659)
            ·
              refine ⟨21841899569665468705353989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14561266379776979136902659 21841899569665468705353989)
              ·
                refine ⟨4095356169312275382253873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21841899569665468705353989 4095356169312275382253873)
                ·
                  refine ⟨3071517126984206536690405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095356169312275382253873 3071517126984206536690405)
                  ·
                    refine ⟨575909461309538725629451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071517126984206536690405 575909461309538725629451)
                    ·
                      rfl

theorem cell23_3364739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4, 2, 4].length) (baseStart_3364739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364739 prefixEnd_3364739 := by exact prefixLift 3364739
  have htrace : WordTrace (prefixWord ++ tailWord_3364739) baseStart_3364739 baseEnd_3364739 := by
    simpa [prefixWord, tailWord_3364739, baseEnd_3364739] using wordTrace_append hprefix tailTrace_3364739
  have hstable : (prefixWord ++ tailWord_3364739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364739).length < 2 ^ (prefixWord ++ tailWord_3364739).sum := by decide
  have hdescent : baseEnd_3364739 < baseStart_3364739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364756 : List Nat := [2, 4, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3364756 : Nat := 118140960795 + 3364756 * 2 ^ 59
def prefixEnd_3364756 : Nat := 4983230072969 + 3 ^ 40 * 3364756 * 2
def baseEnd_3364756 : Nat := 575912371033247536791925

theorem tailTrace_3364756 : CollatzResearch.WordTrace tailWord_3364756 prefixEnd_3364756 575912371033247536791925 := by
  unfold tailWord_3364756
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361366699035570709661061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81815155598714094279548081 61361366699035570709661061)
  ·
    refine ⟨11505256256069169508061449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61361366699035570709661061 11505256256069169508061449)
    ·
      refine ⟨8628942192051877131046087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11505256256069169508061449 8628942192051877131046087)
      ·
        refine ⟨12943413288077815696569131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628942192051877131046087 12943413288077815696569131)
        ·
          refine ⟨19415119932116723544853697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12943413288077815696569131 19415119932116723544853697)
          ·
            refine ⟨14561339949087542658640273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19415119932116723544853697 14561339949087542658640273)
            ·
              refine ⟨10921004961815656993980205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14561339949087542658640273 10921004961815656993980205)
              ·
                refine ⟨4095376860680871372742577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10921004961815656993980205 4095376860680871372742577)
                ·
                  refine ⟨3071532645510653529556933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095376860680871372742577 3071532645510653529556933)
                  ·
                    refine ⟨575912371033247536791925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071532645510653529556933 575912371033247536791925)
                    ·
                      rfl

theorem cell23_3364756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3364756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364756 prefixEnd_3364756 := by exact prefixLift 3364756
  have htrace : WordTrace (prefixWord ++ tailWord_3364756) baseStart_3364756 baseEnd_3364756 := by
    simpa [prefixWord, tailWord_3364756, baseEnd_3364756] using wordTrace_append hprefix tailTrace_3364756
  have hstable : (prefixWord ++ tailWord_3364756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364756).length < 2 ^ (prefixWord ++ tailWord_3364756).sum := by decide
  have hdescent : baseEnd_3364756 < baseStart_3364756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364759 : List Nat := [1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4]
def baseStart_3364759 : Nat := 118140960795 + 3364759 * 2 ^ 59
def prefixEnd_3364759 : Nat := 4983230072969 + 3 ^ 40 * 3364759 * 2
def baseEnd_3364759 : Nat := 1727738653541706098638261

theorem tailTrace_3364759 : CollatzResearch.WordTrace tailWord_3364759 prefixEnd_3364759 1727738653541706098638261 := by
  unfold tailWord_3364759
  simp only [CollatzResearch.WordTrace]
  refine ⟨122722842817060272931681331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81815228544706848621120887 122722842817060272931681331)
  ·
    refine ⟨184084264225590409397521997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122722842817060272931681331 184084264225590409397521997)
    ·
      refine ⟨69031599084596403524070749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184084264225590409397521997 69031599084596403524070749)
      ·
        refine ⟨25886849656723651321526531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69031599084596403524070749 25886849656723651321526531)
        ·
          refine ⟨38830274485085476982289797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25886849656723651321526531 38830274485085476982289797)
          ·
            refine ⟨7280676465953526934179337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38830274485085476982289797 7280676465953526934179337)
            ·
              refine ⟨5460507349465145200634503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7280676465953526934179337 5460507349465145200634503)
              ·
                refine ⟨8190761024197717800951755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5460507349465145200634503 8190761024197717800951755)
                ·
                  refine ⟨12286141536296576701427633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8190761024197717800951755 12286141536296576701427633)
                  ·
                    refine ⟨9214606152222432526070725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12286141536296576701427633 9214606152222432526070725)
                    ·
                      refine ⟨1727738653541706098638261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9214606152222432526070725 1727738653541706098638261)
                      ·
                        rfl

theorem cell23_3364759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_3364759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364759 prefixEnd_3364759 := by exact prefixLift 3364759
  have htrace : WordTrace (prefixWord ++ tailWord_3364759) baseStart_3364759 baseEnd_3364759 := by
    simpa [prefixWord, tailWord_3364759, baseEnd_3364759] using wordTrace_append hprefix tailTrace_3364759
  have hstable : (prefixWord ++ tailWord_3364759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364759).length < 2 ^ (prefixWord ++ tailWord_3364759).sum := by decide
  have hdescent : baseEnd_3364759 < baseStart_3364759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364832 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_3364832 : Nat := 118140960795 + 3364832 * 2 ^ 59
def prefixEnd_3364832 : Nat := 4983230072969 + 3 ^ 40 * 3364832 * 2
def baseEnd_3364832 : Nat := 1727776137629484313025425

theorem tailTrace_3364832 : CollatzResearch.WordTrace tailWord_3364832 prefixEnd_3364832 1727776137629484313025425 := by
  unfold tailWord_3364832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362752672897903199544375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81817003563863870932725833 61362752672897903199544375)
  ·
    refine ⟨92044129009346854799316563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61362752672897903199544375 92044129009346854799316563)
    ·
      refine ⟨138066193514020282198974845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92044129009346854799316563 138066193514020282198974845)
      ·
        refine ⟨51774822567757605824615567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138066193514020282198974845 51774822567757605824615567)
        ·
          refine ⟨77662233851636408736923351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51774822567757605824615567 77662233851636408736923351)
          ·
            refine ⟨116493350777454613105385027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77662233851636408736923351 116493350777454613105385027)
            ·
              refine ⟨174740026166181919658077541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116493350777454613105385027 174740026166181919658077541)
              ·
                refine ⟨32763754906159109935889539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174740026166181919658077541 32763754906159109935889539)
                ·
                  refine ⟨49145632359238664903834309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32763754906159109935889539 49145632359238664903834309)
                  ·
                    refine ⟨9214806067357249669468933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49145632359238664903834309 9214806067357249669468933)
                    ·
                      refine ⟨1727776137629484313025425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9214806067357249669468933 1727776137629484313025425)
                      ·
                        rfl

theorem cell23_3364832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_3364832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364832 prefixEnd_3364832 := by exact prefixLift 3364832
  have htrace : WordTrace (prefixWord ++ tailWord_3364832) baseStart_3364832 baseEnd_3364832 := by
    simpa [prefixWord, tailWord_3364832, baseEnd_3364832] using wordTrace_append hprefix tailTrace_3364832
  have hstable : (prefixWord ++ tailWord_3364832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364832).length < 2 ^ (prefixWord ++ tailWord_3364832).sum := by decide
  have hdescent : baseEnd_3364832 < baseStart_3364832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364836 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_3364836 : Nat := 118140960795 + 3364836 * 2 ^ 59
def prefixEnd_3364836 : Nat := 4983230072969 + 3 ^ 40 * 3364836 * 2
def baseEnd_3364836 : Nat := 1727778191552102297375407

theorem tailTrace_3364836 : CollatzResearch.WordTrace tailWord_3364836 prefixEnd_3364836 1727778191552102297375407 := by
  unfold tailWord_3364836
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362825618890657541117181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81817100825187543388156241 61362825618890657541117181)
  ·
    refine ⟨23011059607083996577918943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61362825618890657541117181 23011059607083996577918943)
    ·
      refine ⟨34516589410625994866878415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23011059607083996577918943 34516589410625994866878415)
      ·
        refine ⟨51774884115938992300317623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34516589410625994866878415 51774884115938992300317623)
        ·
          refine ⟨77662326173908488450476435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51774884115938992300317623 77662326173908488450476435)
          ·
            refine ⟨116493489260862732675714653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77662326173908488450476435 116493489260862732675714653)
            ·
              refine ⟨43685058472823524753392995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116493489260862732675714653 43685058472823524753392995)
              ·
                refine ⟨65527587709235287130089493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43685058472823524753392995 65527587709235287130089493)
                ·
                  refine ⟨3071605673870404084222945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65527587709235287130089493 3071605673870404084222945)
                  ·
                    refine ⟨2303704255402803063167209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3071605673870404084222945 2303704255402803063167209)
                    ·
                      refine ⟨1727778191552102297375407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303704255402803063167209 1727778191552102297375407)
                      ·
                        rfl

theorem cell23_3364836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_3364836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364836 prefixEnd_3364836 := by exact prefixLift 3364836
  have htrace : WordTrace (prefixWord ++ tailWord_3364836) baseStart_3364836 baseEnd_3364836 := by
    simpa [prefixWord, tailWord_3364836, baseEnd_3364836] using wordTrace_append hprefix tailTrace_3364836
  have hstable : (prefixWord ++ tailWord_3364836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364836).length < 2 ^ (prefixWord ++ tailWord_3364836).sum := by decide
  have hdescent : baseEnd_3364836 < baseStart_3364836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364859 : List Nat := [1, 1, 1, 1, 1, 3, 4, 6, 5]
def baseStart_3364859 : Nat := 118140960795 + 3364859 * 2 ^ 59
def prefixEnd_3364859 : Nat := 4983230072969 + 3 ^ 40 * 3364859 * 2
def baseEnd_3364859 : Nat := 191976666845239523043089

theorem tailTrace_3364859 : CollatzResearch.WordTrace tailWord_3364859 prefixEnd_3364859 191976666845239523043089 := by
  unfold tailWord_3364859
  simp only [CollatzResearch.WordTrace]
  refine ⟨122726490116697990010321631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81817660077798660006881087 122726490116697990010321631)
  ·
    refine ⟨184089735175046985015482447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122726490116697990010321631 184089735175046985015482447)
    ·
      refine ⟨276134602762570477523223671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184089735175046985015482447 276134602762570477523223671)
      ·
        refine ⟨414201904143855716284835507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276134602762570477523223671 414201904143855716284835507)
        ·
          refine ⟨621302856215783574427253261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414201904143855716284835507 621302856215783574427253261)
          ·
            refine ⟨232988571080918840410219973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621302856215783574427253261 232988571080918840410219973)
            ·
              refine ⟨43685357077672282576916245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 232988571080918840410219973 43685357077672282576916245)
              ·
                refine ⟨2047751113015888245792949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43685357077672282576916245 2047751113015888245792949)
                ·
                  refine ⟨191976666845239523043089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2047751113015888245792949 191976666845239523043089)
                  ·
                    rfl

theorem cell23_3364859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 6, 5].length) (baseStart_3364859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364859 prefixEnd_3364859 := by exact prefixLift 3364859
  have htrace : WordTrace (prefixWord ++ tailWord_3364859) baseStart_3364859 baseEnd_3364859 := by
    simpa [prefixWord, tailWord_3364859, baseEnd_3364859] using wordTrace_append hprefix tailTrace_3364859
  have hstable : (prefixWord ++ tailWord_3364859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364859).length < 2 ^ (prefixWord ++ tailWord_3364859).sum := by decide
  have hdescent : baseEnd_3364859 < baseStart_3364859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364906 : List Nat := [3, 1, 4, 1, 2, 1, 2, 2, 2, 5]
def baseStart_3364906 : Nat := 118140960795 + 3364906 * 2 ^ 59
def prefixEnd_3364906 : Nat := 4983230072969 + 3 ^ 40 * 3364906 * 2
def baseEnd_3364906 : Nat := 575938045065972341166695

theorem tailTrace_3364906 : CollatzResearch.WordTrace tailWord_3364906 prefixEnd_3364906 575938045065972341166695 := by
  unfold tailWord_3364906
  simp only [CollatzResearch.WordTrace]
  refine ⟨30682051086881929259320643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81818802898351811358188381 30682051086881929259320643)
  ·
    refine ⟨46023076630322893888980965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30682051086881929259320643 46023076630322893888980965)
    ·
      refine ⟨8629326868185542604183931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46023076630322893888980965 8629326868185542604183931)
      ·
        refine ⟨12943990302278313906275897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8629326868185542604183931 12943990302278313906275897)
        ·
          refine ⟨9707992726708735429706923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12943990302278313906275897 9707992726708735429706923)
          ·
            refine ⟨14561989090063103144560385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9707992726708735429706923 14561989090063103144560385)
            ·
              refine ⟨10921491817547327358420289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14561989090063103144560385 10921491817547327358420289)
              ·
                refine ⟨8191118863160495518815217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10921491817547327358420289 8191118863160495518815217)
                ·
                  refine ⟨6143339147370371639111413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8191118863160495518815217 6143339147370371639111413)
                  ·
                    refine ⟨575938045065972341166695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6143339147370371639111413 575938045065972341166695)
                    ·
                      rfl

theorem cell23_3364906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 2, 5].length) (baseStart_3364906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364906 prefixEnd_3364906 := by exact prefixLift 3364906
  have htrace : WordTrace (prefixWord ++ tailWord_3364906) baseStart_3364906 baseEnd_3364906 := by
    simpa [prefixWord, tailWord_3364906, baseEnd_3364906] using wordTrace_append hprefix tailTrace_3364906
  have hstable : (prefixWord ++ tailWord_3364906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364906).length < 2 ^ (prefixWord ++ tailWord_3364906).sum := by decide
  have hdescent : baseEnd_3364906 < baseStart_3364906 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364910 : List Nat := [4, 1, 3, 1, 1, 4, 2, 2, 5]
def baseStart_3364910 : Nat := 118140960795 + 3364910 * 2 ^ 59
def prefixEnd_3364910 : Nat := 4983230072969 + 3 ^ 40 * 3364910 * 2
def baseEnd_3364910 : Nat := 191979576568948334205563

theorem tailTrace_3364910 : CollatzResearch.WordTrace tailWord_3364910 prefixEnd_3364910 191979576568948334205563 := by
  unfold tailWord_3364910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341043779939153215053523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81818900159675483813618789 15341043779939153215053523)
  ·
    refine ⟨23011565669908729822580285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341043779939153215053523 23011565669908729822580285)
    ·
      refine ⟨8629337126215773683467607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23011565669908729822580285 8629337126215773683467607)
      ·
        refine ⟨12944005689323660525201411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8629337126215773683467607 12944005689323660525201411)
        ·
          refine ⟨19416008533985490787802117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12944005689323660525201411 19416008533985490787802117)
          ·
            refine ⟨3640501600122279522712897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19416008533985490787802117 3640501600122279522712897)
            ·
              refine ⟨2730376200091709642034673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640501600122279522712897 2730376200091709642034673)
              ·
                refine ⟨2047782150068782231526005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730376200091709642034673 2047782150068782231526005)
                ·
                  refine ⟨191979576568948334205563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2047782150068782231526005 191979576568948334205563)
                  ·
                    rfl

theorem cell23_3364910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 4, 2, 2, 5].length) (baseStart_3364910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364910 prefixEnd_3364910 := by exact prefixLift 3364910
  have htrace : WordTrace (prefixWord ++ tailWord_3364910) baseStart_3364910 baseEnd_3364910 := by
    simpa [prefixWord, tailWord_3364910, baseEnd_3364910] using wordTrace_append hprefix tailTrace_3364910
  have hstable : (prefixWord ++ tailWord_3364910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364910).length < 2 ^ (prefixWord ++ tailWord_3364910).sum := by decide
  have hdescent : baseEnd_3364910 < baseStart_3364910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364953 : List Nat := [1, 2, 1, 2, 2, 1, 6, 3, 1, 4]
def baseStart_3364953 : Nat := 118140960795 + 3364953 * 2 ^ 59
def prefixEnd_3364953 : Nat := 4983230072969 + 3 ^ 40 * 3364953 * 2
def baseEnd_3364953 : Nat := 575946089596226113204123

theorem tailTrace_3364953 : CollatzResearch.WordTrace tailWord_3364953 prefixEnd_3364953 575946089596226113204123 := by
  unfold tailWord_3364953
  simp only [CollatzResearch.WordTrace]
  refine ⟨122729918578357444064243513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81819945718904962709495675 122729918578357444064243513)
  ·
    refine ⟨92047438933768083048182635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122729918578357444064243513 92047438933768083048182635)
    ·
      refine ⟨138071158400652124572273953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92047438933768083048182635 138071158400652124572273953)
      ·
        refine ⟨103553368800489093429205465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138071158400652124572273953 103553368800489093429205465)
        ·
          refine ⟨77665026600366820071904099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103553368800489093429205465 77665026600366820071904099)
          ·
            refine ⟨116497539900550230107856149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77665026600366820071904099 116497539900550230107856149)
            ·
              refine ⟨5460822182838292036305757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116497539900550230107856149 5460822182838292036305757)
              ·
                refine ⟨2047808318564359513614659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5460822182838292036305757 2047808318564359513614659)
                ·
                  refine ⟨3071712477846539270421989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047808318564359513614659 3071712477846539270421989)
                  ·
                    refine ⟨575946089596226113204123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071712477846539270421989 575946089596226113204123)
                    ·
                      rfl

theorem cell23_3364953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 3, 1, 4].length) (baseStart_3364953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364953 prefixEnd_3364953 := by exact prefixLift 3364953
  have htrace : WordTrace (prefixWord ++ tailWord_3364953) baseStart_3364953 baseEnd_3364953 := by
    simpa [prefixWord, tailWord_3364953, baseEnd_3364953] using wordTrace_append hprefix tailTrace_3364953
  have hstable : (prefixWord ++ tailWord_3364953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364953).length < 2 ^ (prefixWord ++ tailWord_3364953).sum := by decide
  have hdescent : baseEnd_3364953 < baseStart_3364953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365029 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 6]
def baseStart_3365029 : Nat := 118140960795 + 3365029 * 2 ^ 59
def prefixEnd_3365029 : Nat := 4983230072969 + 3 ^ 40 * 3365029 * 2
def baseEnd_3365029 : Nat := 1727877293318420042262019

theorem tailTrace_3365029 : CollatzResearch.WordTrace tailWord_3365029 prefixEnd_3365029 1727877293318420042262019 := by
  unfold tailWord_3365029
  simp only [CollatzResearch.WordTrace]
  refine ⟨122732690526082109044010141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81821793684054739362673427 122732690526082109044010141)
  ·
    refine ⟨46024758947280790891503803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122732690526082109044010141 46024758947280790891503803)
    ·
      refine ⟨69037138420921186337255705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46024758947280790891503803 69037138420921186337255705)
      ·
        refine ⟨51777853815690889752941779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69037138420921186337255705 51777853815690889752941779)
        ·
          refine ⟨77666780723536334629412669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51777853815690889752941779 77666780723536334629412669)
          ·
            refine ⟨29125042771326125486029751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77666780723536334629412669 29125042771326125486029751)
            ·
              refine ⟨43687564156989188229044627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29125042771326125486029751 43687564156989188229044627)
              ·
                refine ⟨65531346235483782343566941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43687564156989188229044627 65531346235483782343566941)
                ·
                  refine ⟨24574254838306418378837603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65531346235483782343566941 24574254838306418378837603)
                  ·
                    refine ⟨36861382257459627568256405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24574254838306418378837603 36861382257459627568256405)
                    ·
                      refine ⟨1727877293318420042262019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36861382257459627568256405 1727877293318420042262019)
                      ·
                        rfl

theorem cell23_3365029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_3365029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365029 prefixEnd_3365029 := by exact prefixLift 3365029
  have htrace : WordTrace (prefixWord ++ tailWord_3365029) baseStart_3365029 baseEnd_3365029 := by
    simpa [prefixWord, tailWord_3365029, baseEnd_3365029] using wordTrace_append hprefix tailTrace_3365029
  have hstable : (prefixWord ++ tailWord_3365029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365029).length < 2 ^ (prefixWord ++ tailWord_3365029).sum := by decide
  have hdescent : baseEnd_3365029 < baseStart_3365029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365083 : List Nat := [1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 3]
def baseStart_3365083 : Nat := 118140960795 + 3365083 * 2 ^ 59
def prefixEnd_3365083 : Nat := 4983230072969 + 3 ^ 40 * 3365083 * 2
def baseEnd_3365083 : Nat := 1727905021273762830986771

theorem tailTrace_3365083 : CollatzResearch.WordTrace tailWord_3365083 prefixEnd_3365083 1727905021273762830986771 := by
  unfold tailWord_3365083
  simp only [CollatzResearch.WordTrace]
  refine ⟨122734660067886476266475903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81823106711924317510983935 122734660067886476266475903)
  ·
    refine ⟨184101990101829714399713855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122734660067886476266475903 184101990101829714399713855)
    ·
      refine ⟨276152985152744571599570783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184101990101829714399713855 276152985152744571599570783)
      ·
        refine ⟨414229477729116857399356175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276152985152744571599570783 414229477729116857399356175)
        ·
          refine ⟨621344216593675286099034263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414229477729116857399356175 621344216593675286099034263)
          ·
            refine ⟨932016324890512929148551395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621344216593675286099034263 932016324890512929148551395)
            ·
              refine ⟨1398024487335769393722827093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 932016324890512929148551395 1398024487335769393722827093)
              ·
                refine ⟨4095774865241511895672345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1398024487335769393722827093 4095774865241511895672345)
                ·
                  refine ⟨3071831148931133921754259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4095774865241511895672345 3071831148931133921754259)
                  ·
                    refine ⟨4607746723396700882631389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3071831148931133921754259 4607746723396700882631389)
                    ·
                      refine ⟨1727905021273762830986771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4607746723396700882631389 1727905021273762830986771)
                      ·
                        rfl

theorem cell23_3365083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 10, 2, 1, 3].length) (baseStart_3365083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365083 prefixEnd_3365083 := by exact prefixLift 3365083
  have htrace : WordTrace (prefixWord ++ tailWord_3365083) baseStart_3365083 baseEnd_3365083 := by
    simpa [prefixWord, tailWord_3365083, baseEnd_3365083] using wordTrace_append hprefix tailTrace_3365083
  have hstable : (prefixWord ++ tailWord_3365083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365083).length < 2 ^ (prefixWord ++ tailWord_3365083).sum := by decide
  have hdescent : baseEnd_3365083 < baseStart_3365083 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365110 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_3365110 : Nat := 118140960795 + 3365110 * 2 ^ 59
def prefixEnd_3365110 : Nat := 4983230072969 + 3 ^ 40 * 3365110 * 2
def baseEnd_3365110 : Nat := 1727918885251434225349147

theorem tailTrace_3365110 : CollatzResearch.WordTrace tailWord_3365110 prefixEnd_3365110 1727918885251434225349147 := by
  unfold tailWord_3365110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670977802424291242356799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81823763225859106585139189 7670977802424291242356799)
  ·
    refine ⟨11506466703636436863535199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7670977802424291242356799 11506466703636436863535199)
    ·
      refine ⟨17259700055454655295302799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11506466703636436863535199 17259700055454655295302799)
      ·
        refine ⟨25889550083181982942954199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17259700055454655295302799 25889550083181982942954199)
        ·
          refine ⟨38834325124772974414431299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25889550083181982942954199 38834325124772974414431299)
          ·
            refine ⟨58251487687159461621646949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38834325124772974414431299 58251487687159461621646949)
            ·
              refine ⟨10922153941342399054058803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58251487687159461621646949 10922153941342399054058803)
              ·
                refine ⟨16383230912013598581088205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922153941342399054058803 16383230912013598581088205)
                ·
                  refine ⟨6143711592005099467908077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16383230912013598581088205 6143711592005099467908077)
                  ·
                    refine ⟨2303891847001912300465529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6143711592005099467908077 2303891847001912300465529)
                    ·
                      refine ⟨1727918885251434225349147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303891847001912300465529 1727918885251434225349147)
                      ·
                        rfl

theorem cell23_3365110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_3365110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365110 prefixEnd_3365110 := by exact prefixLift 3365110
  have htrace : WordTrace (prefixWord ++ tailWord_3365110) baseStart_3365110 baseEnd_3365110 := by
    simpa [prefixWord, tailWord_3365110, baseEnd_3365110] using wordTrace_append hprefix tailTrace_3365110
  have hstable : (prefixWord ++ tailWord_3365110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365110).length < 2 ^ (prefixWord ++ tailWord_3365110).sum := by decide
  have hdescent : baseEnd_3365110 < baseStart_3365110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365123 : List Nat := [1, 1, 1, 3, 2, 3, 1, 4, 1, 4, 2]
def baseStart_3365123 : Nat := 118140960795 + 3365123 * 2 ^ 59
def prefixEnd_3365123 : Nat := 4983230072969 + 3 ^ 40 * 3365123 * 2
def baseEnd_3365123 : Nat := 1727925560499942674486587

theorem tailTrace_3365123 : CollatzResearch.WordTrace tailWord_3365123 prefixEnd_3365123 1727925560499942674486587 := by
  unfold tailWord_3365123
  simp only [CollatzResearch.WordTrace]
  refine ⟨122736118987741563097932023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81824079325161042065288015 122736118987741563097932023)
  ·
    refine ⟨184104178481612344646898035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122736118987741563097932023 184104178481612344646898035)
    ·
      refine ⟨276156267722418516970347053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184104178481612344646898035 276156267722418516970347053)
      ·
        refine ⟨103558600395906943863880145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276156267722418516970347053 103558600395906943863880145)
        ·
          refine ⟨77668950296930207897910109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103558600395906943863880145 77668950296930207897910109)
          ·
            refine ⟨29125856361348827961716291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77668950296930207897910109 29125856361348827961716291)
            ·
              refine ⟨43688784542023241942574437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29125856361348827961716291 43688784542023241942574437)
              ·
                refine ⟨8191647101629357864232707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43688784542023241942574437 8191647101629357864232707)
                ·
                  refine ⟨12287470652444036796349061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191647101629357864232707 12287470652444036796349061)
                  ·
                    refine ⟨2303900747333256899315449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12287470652444036796349061 2303900747333256899315449)
                    ·
                      refine ⟨1727925560499942674486587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303900747333256899315449 1727925560499942674486587)
                      ·
                        rfl

theorem cell23_3365123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 4, 2].length) (baseStart_3365123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365123 prefixEnd_3365123 := by exact prefixLift 3365123
  have htrace : WordTrace (prefixWord ++ tailWord_3365123) baseStart_3365123 baseEnd_3365123 := by
    simpa [prefixWord, tailWord_3365123, baseEnd_3365123] using wordTrace_append hprefix tailTrace_3365123
  have hstable : (prefixWord ++ tailWord_3365123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365123).length < 2 ^ (prefixWord ++ tailWord_3365123).sum := by decide
  have hdescent : baseEnd_3365123 < baseStart_3365123 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365150 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3365150 : Nat := 118140960795 + 3365150 * 2 ^ 59
def prefixEnd_3365150 : Nat := 4983230072969 + 3 ^ 40 * 3365150 * 2
def baseEnd_3365150 : Nat := 575979808159204689616321

theorem tailTrace_3365150 : CollatzResearch.WordTrace tailWord_3365150 prefixEnd_3365150 575979808159204689616321 := by
  unfold tailWord_3365150
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342137969830468338645613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81824735839095831139443269 15342137969830468338645613)
  ·
    refine ⟨5753301738686425626992105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15342137969830468338645613 5753301738686425626992105)
    ·
      refine ⟨4314976304014819220244079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5753301738686425626992105 4314976304014819220244079)
      ·
        refine ⟨6472464456022228830366119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4314976304014819220244079 6472464456022228830366119)
        ·
          refine ⟨9708696684033343245549179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472464456022228830366119 9708696684033343245549179)
          ·
            refine ⟨14563045026050014868323769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9708696684033343245549179 14563045026050014868323769)
            ·
              refine ⟨10922283769537511151242827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14563045026050014868323769 10922283769537511151242827)
              ·
                refine ⟨16383425654306266726864241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922283769537511151242827 16383425654306266726864241)
                ·
                  refine ⟨12287569240729700045148181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16383425654306266726864241 12287569240729700045148181)
                  ·
                    refine ⟨575979808159204689616321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12287569240729700045148181 575979808159204689616321)
                    ·
                      rfl

theorem cell23_3365150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3365150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365150 prefixEnd_3365150 := by exact prefixLift 3365150
  have htrace : WordTrace (prefixWord ++ tailWord_3365150) baseStart_3365150 baseEnd_3365150 := by
    simpa [prefixWord, tailWord_3365150, baseEnd_3365150] using wordTrace_append hprefix tailTrace_3365150
  have hstable : (prefixWord ++ tailWord_3365150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365150).length < 2 ^ (prefixWord ++ tailWord_3365150).sum := by decide
  have hdescent : baseEnd_3365150 < baseStart_3365150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365157 : List Nat := [1, 3, 1, 2, 5, 2, 1, 1, 1, 4, 2]
def baseStart_3365157 : Nat := 118140960795 + 3365157 * 2 ^ 59
def prefixEnd_3365157 : Nat := 4983230072969 + 3 ^ 40 * 3365157 * 2
def baseEnd_3365157 : Nat := 1727943018842195541461431

theorem tailTrace_3365157 : CollatzResearch.WordTrace tailWord_3365157 prefixEnd_3365157 1727943018842195541461431 := by
  unfold tailWord_3365157
  simp only [CollatzResearch.WordTrace]
  refine ⟨122737359069618386904669725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81824906046412257936446483 122737359069618386904669725)
  ·
    refine ⟨46026509651106895089251147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122737359069618386904669725 46026509651106895089251147)
    ·
      refine ⟨69039764476660342633876721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46026509651106895089251147 69039764476660342633876721)
      ·
        refine ⟨51779823357495256975407541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69039764476660342633876721 51779823357495256975407541)
        ·
          refine ⟨4854358439765180341444457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51779823357495256975407541 4854358439765180341444457)
          ·
            refine ⟨3640768829823885256083343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4854358439765180341444457 3640768829823885256083343)
            ·
              refine ⟨5461153244735827884125015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3640768829823885256083343 5461153244735827884125015)
              ·
                refine ⟨8191729867103741826187523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461153244735827884125015 8191729867103741826187523)
                ·
                  refine ⟨12287594800655612739281285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8191729867103741826187523 12287594800655612739281285)
                  ·
                    refine ⟨2303924025122927388615241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12287594800655612739281285 2303924025122927388615241)
                    ·
                      refine ⟨1727943018842195541461431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303924025122927388615241 1727943018842195541461431)
                      ·
                        rfl

theorem cell23_3365157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_3365157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365157 prefixEnd_3365157 := by exact prefixLift 3365157
  have htrace : WordTrace (prefixWord ++ tailWord_3365157) baseStart_3365157 baseEnd_3365157 := by
    simpa [prefixWord, tailWord_3365157, baseEnd_3365157] using wordTrace_append hprefix tailTrace_3365157
  have hstable : (prefixWord ++ tailWord_3365157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365157).length < 2 ^ (prefixWord ++ tailWord_3365157).sum := by decide
  have hdescent : baseEnd_3365157 < baseStart_3365157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365176 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_3365176 : Nat := 118140960795 + 3365176 * 2 ^ 59
def prefixEnd_3365176 : Nat := 4983230072969 + 3 ^ 40 * 3365176 * 2
def baseEnd_3365176 : Nat := 575984258324876989041281

theorem tailTrace_3365176 : CollatzResearch.WordTrace tailWord_3365176 prefixEnd_3365176 575984258324876989041281 := by
  unfold tailWord_3365176
  simp only [CollatzResearch.WordTrace]
  refine ⟨61369026028274776574805691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81825368037699702099740921 61369026028274776574805691)
  ·
    refine ⟨92053539042412164862208537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61369026028274776574805691 92053539042412164862208537)
    ·
      refine ⟨69040154281809123646656403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92053539042412164862208537 69040154281809123646656403)
      ·
        refine ⟨103560231422713685469984605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69040154281809123646656403 103560231422713685469984605)
        ·
          refine ⟨38835086783517632051244227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103560231422713685469984605 38835086783517632051244227)
          ·
            refine ⟨58252630175276448076866341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38835086783517632051244227 58252630175276448076866341)
            ·
              refine ⟨10922368157864334014412439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58252630175276448076866341 10922368157864334014412439)
              ·
                refine ⟨16383552236796501021618659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922368157864334014412439 16383552236796501021618659)
                ·
                  refine ⟨24575328355194751532427989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16383552236796501021618659 24575328355194751532427989)
                  ·
                    refine ⟨575984258324876989041281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24575328355194751532427989 575984258324876989041281)
                    ·
                      rfl

theorem cell23_3365176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_3365176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365176 prefixEnd_3365176 := by exact prefixLift 3365176
  have htrace : WordTrace (prefixWord ++ tailWord_3365176) baseStart_3365176 baseEnd_3365176 := by
    simpa [prefixWord, tailWord_3365176, baseEnd_3365176] using wordTrace_append hprefix tailTrace_3365176
  have hstable : (prefixWord ++ tailWord_3365176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365176).length < 2 ^ (prefixWord ++ tailWord_3365176).sum := by decide
  have hdescent : baseEnd_3365176 < baseStart_3365176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365257 : List Nat := [1, 2, 1, 1, 6, 2, 1, 4, 1, 4]
def baseStart_3365257 : Nat := 118140960795 + 3365257 * 2 ^ 59
def prefixEnd_3365257 : Nat := 4983230072969 + 3 ^ 40 * 3365257 * 2
def baseEnd_3365257 : Nat := 575998122302548383403657

theorem tailTrace_3365257 : CollatzResearch.WordTrace tailWord_3365257 prefixEnd_3365257 575998122302548383403657 := by
  unfold tailWord_3365257
  simp only [CollatzResearch.WordTrace]
  refine ⟨122741006369256103983310025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81827337579504069322206683 122741006369256103983310025)
  ·
    refine ⟨92055754776942077987482519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122741006369256103983310025 92055754776942077987482519)
    ·
      refine ⟨138083632165413116981223779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92055754776942077987482519 138083632165413116981223779)
      ·
        refine ⟨207125448248119675471835669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138083632165413116981223779 207125448248119675471835669)
        ·
          refine ⟨9709005386630609787742297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 207125448248119675471835669 9709005386630609787742297)
          ·
            refine ⟨7281754039972957340806723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9709005386630609787742297 7281754039972957340806723)
            ·
              refine ⟨10922631059959436011210085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281754039972957340806723 10922631059959436011210085)
              ·
                refine ⟨2047993323742394252101891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10922631059959436011210085 2047993323742394252101891)
                ·
                  refine ⟨3071989985613591378152837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2047993323742394252101891 3071989985613591378152837)
                  ·
                    refine ⟨575998122302548383403657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3071989985613591378152837 575998122302548383403657)
                    ·
                      rfl

theorem cell23_3365257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 4, 1, 4].length) (baseStart_3365257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365257 prefixEnd_3365257 := by exact prefixLift 3365257
  have htrace : WordTrace (prefixWord ++ tailWord_3365257) baseStart_3365257 baseEnd_3365257 := by
    simpa [prefixWord, tailWord_3365257, baseEnd_3365257] using wordTrace_append hprefix tailTrace_3365257
  have hstable : (prefixWord ++ tailWord_3365257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365257).length < 2 ^ (prefixWord ++ tailWord_3365257).sum := by decide
  have hdescent : baseEnd_3365257 < baseStart_3365257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365280 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3]
def baseStart_3365280 : Nat := 118140960795 + 3365280 * 2 ^ 59
def prefixEnd_3365280 : Nat := 4983230072969 + 3 ^ 40 * 3365280 * 2
def baseEnd_3365280 : Nat := 1728006176962698560223365

theorem tailTrace_3365280 : CollatzResearch.WordTrace tailWord_3365280 prefixEnd_3365280 1728006176962698560223365 := by
  unfold tailWord_3365280
  simp only [CollatzResearch.WordTrace]
  refine ⟨61370922624086389455698647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81827896832115185940931529 61370922624086389455698647)
  ·
    refine ⟨92056383936129584183547971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61370922624086389455698647 92056383936129584183547971)
    ·
      refine ⟨138084575904194376275321957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92056383936129584183547971 138084575904194376275321957)
      ·
        refine ⟨25890857982036445551622867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138084575904194376275321957 25890857982036445551622867)
        ·
          refine ⟨38836286973054668327434301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25890857982036445551622867 38836286973054668327434301)
          ·
            refine ⟨14563607614895500622787863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38836286973054668327434301 14563607614895500622787863)
            ·
              refine ⟨21845411422343250934181795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14563607614895500622787863 21845411422343250934181795)
              ·
                refine ⟨32768117133514876401272693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21845411422343250934181795 32768117133514876401272693)
                ·
                  refine ⟨3072010981267019662619315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32768117133514876401272693 3072010981267019662619315)
                  ·
                    refine ⟨4608016471900529493928973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3072010981267019662619315 4608016471900529493928973)
                    ·
                      refine ⟨1728006176962698560223365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4608016471900529493928973 1728006176962698560223365)
                      ·
                        rfl

theorem cell23_3365280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_3365280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365280 prefixEnd_3365280 := by exact prefixLift 3365280
  have htrace : WordTrace (prefixWord ++ tailWord_3365280) baseStart_3365280 baseEnd_3365280 := by
    simpa [prefixWord, tailWord_3365280, baseEnd_3365280] using wordTrace_append hprefix tailTrace_3365280
  have hstable : (prefixWord ++ tailWord_3365280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365280).length < 2 ^ (prefixWord ++ tailWord_3365280).sum := by decide
  have hdescent : baseEnd_3365280 < baseStart_3365280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365283 : List Nat := [1, 1, 1, 4, 1, 4, 2, 1, 3, 5]
def baseStart_3365283 : Nat := 118140960795 + 3365283 * 2 ^ 59
def prefixEnd_3365283 : Nat := 4983230072969 + 3 ^ 40 * 3365283 * 2
def baseEnd_3365283 : Nat := 576002572468220682828617

theorem tailTrace_3365283 : CollatzResearch.WordTrace tailWord_3365283 prefixEnd_3365283 576002572468220682828617 := by
  unfold tailWord_3365283
  simp only [CollatzResearch.WordTrace]
  refine ⟨122741954667161910423756503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81827969778107940282504335 122741954667161910423756503)
  ·
    refine ⟨184112932000742865635634755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122741954667161910423756503 184112932000742865635634755)
    ·
      refine ⟨276169398001114298453452133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184112932000742865635634755 276169398001114298453452133)
      ·
        refine ⟨51781762125208930960022275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276169398001114298453452133 51781762125208930960022275)
        ·
          refine ⟨77672643187813396440033413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51781762125208930960022275 77672643187813396440033413)
          ·
            refine ⟨14563620597715011832506265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77672643187813396440033413 14563620597715011832506265)
            ·
              refine ⟨10922715448286258874379699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14563620597715011832506265 10922715448286258874379699)
              ·
                refine ⟨16384073172429388311569549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10922715448286258874379699 16384073172429388311569549)
                ·
                  refine ⟨6144027439661020616838581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16384073172429388311569549 6144027439661020616838581)
                  ·
                    refine ⟨576002572468220682828617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6144027439661020616838581 576002572468220682828617)
                    ·
                      rfl

theorem cell23_3365283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 5].length) (baseStart_3365283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365283 prefixEnd_3365283 := by exact prefixLift 3365283
  have htrace : WordTrace (prefixWord ++ tailWord_3365283) baseStart_3365283 baseEnd_3365283 := by
    simpa [prefixWord, tailWord_3365283, baseEnd_3365283] using wordTrace_append hprefix tailTrace_3365283
  have hstable : (prefixWord ++ tailWord_3365283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365283).length < 2 ^ (prefixWord ++ tailWord_3365283).sum := by decide
  have hdescent : baseEnd_3365283 < baseStart_3365283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365296 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_3365296 : Nat := 118140960795 + 3365296 * 2 ^ 59
def prefixEnd_3365296 : Nat := 4983230072969 + 3 ^ 40 * 3365296 * 2
def baseEnd_3365296 : Nat := 576004797551056832541097

theorem tailTrace_3365296 : CollatzResearch.WordTrace tailWord_3365296 prefixEnd_3365296 576004797551056832541097 := by
  unfold tailWord_3365296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61371214408057406821989871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81828285877409875762653161 61371214408057406821989871)
  ·
    refine ⟨92056821612086110232984807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61371214408057406821989871 92056821612086110232984807)
    ·
      refine ⟨138085232418129165349477211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92056821612086110232984807 138085232418129165349477211)
      ·
        refine ⟨207127848627193748024215817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138085232418129165349477211 207127848627193748024215817)
        ·
          refine ⟨155345886470395311018161863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207127848627193748024215817 155345886470395311018161863)
          ·
            refine ⟨233018829705592966527242795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155345886470395311018161863 233018829705592966527242795)
            ·
              refine ⟨349528244558389449790864193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233018829705592966527242795 349528244558389449790864193)
              ·
                refine ⟨262146183418792087343148145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349528244558389449790864193 262146183418792087343148145)
                ·
                  refine ⟨196609637564094065507361109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262146183418792087343148145 196609637564094065507361109)
                  ·
                    refine ⟨576004797551056832541097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 196609637564094065507361109 576004797551056832541097)
                    ·
                      rfl

theorem cell23_3365296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_3365296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365296 prefixEnd_3365296 := by exact prefixLift 3365296
  have htrace : WordTrace (prefixWord ++ tailWord_3365296) baseStart_3365296 baseEnd_3365296 := by
    simpa [prefixWord, tailWord_3365296, baseEnd_3365296] using wordTrace_append hprefix tailTrace_3365296
  have hstable : (prefixWord ++ tailWord_3365296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365296).length < 2 ^ (prefixWord ++ tailWord_3365296).sum := by decide
  have hdescent : baseEnd_3365296 < baseStart_3365296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365337 : List Nat := [1, 2, 1, 2, 4, 1, 1, 4, 3, 2, 2]
def baseStart_3365337 : Nat := 118140960795 + 3365337 * 2 ^ 59
def prefixEnd_3365337 : Nat := 4983230072969 + 3 ^ 40 * 3365337 * 2
def baseEnd_3365337 : Nat := 1728035445360004837210603

theorem tailTrace_3365337 : CollatzResearch.WordTrace tailWord_3365337 prefixEnd_3365337 1728035445360004837210603 := by
  unfold tailWord_3365337
  simp only [CollatzResearch.WordTrace]
  refine ⟨122743924208966277646222265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81829282805977518430814843 122743924208966277646222265)
  ·
    refine ⟨92057943156724708234666699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122743924208966277646222265 92057943156724708234666699)
    ·
      refine ⟨138086914735087062352000049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92057943156724708234666699 138086914735087062352000049)
      ·
        refine ⟨103565186051315296764000037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138086914735087062352000049 103565186051315296764000037)
        ·
          refine ⟨19418472384621618143250007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103565186051315296764000037 19418472384621618143250007)
          ·
            refine ⟨29127708576932427214875011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19418472384621618143250007 29127708576932427214875011)
            ·
              refine ⟨43691562865398640822312517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29127708576932427214875011 43691562865398640822312517)
              ·
                refine ⟨8192168037262245154183597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43691562865398640822312517 8192168037262245154183597)
                ·
                  refine ⟨3072063013973341932818849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8192168037262245154183597 3072063013973341932818849)
                  ·
                    refine ⟨2304047260480006449614137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072063013973341932818849 2304047260480006449614137)
                    ·
                      refine ⟨1728035445360004837210603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304047260480006449614137 1728035445360004837210603)
                      ·
                        rfl

theorem cell23_3365337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_3365337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365337 prefixEnd_3365337 := by exact prefixLift 3365337
  have htrace : WordTrace (prefixWord ++ tailWord_3365337) baseStart_3365337 baseEnd_3365337 := by
    simpa [prefixWord, tailWord_3365337, baseEnd_3365337] using wordTrace_append hprefix tailTrace_3365337
  have hstable : (prefixWord ++ tailWord_3365337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365337).length < 2 ^ (prefixWord ++ tailWord_3365337).sum := by decide
  have hdescent : baseEnd_3365337 < baseStart_3365337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365343 : List Nat := [1, 1, 2, 3, 3, 3, 1, 9]
def baseStart_3365343 : Nat := 118140960795 + 3365343 * 2 ^ 59
def prefixEnd_3365343 : Nat := 4983230072969 + 3 ^ 40 * 3365343 * 2
def baseEnd_3365343 : Nat := 64001426897923400508725

theorem tailTrace_3365343 : CollatzResearch.WordTrace tailWord_3365343 prefixEnd_3365343 64001426897923400508725 := by
  unfold tailWord_3365343
  simp only [CollatzResearch.WordTrace]
  refine ⟨122744143046944540670940683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81829428697963027113960455 122744143046944540670940683)
  ·
    refine ⟨184116214570416811006411025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122744143046944540670940683 184116214570416811006411025)
    ·
      refine ⟨138087160927812608254808269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184116214570416811006411025 138087160927812608254808269)
      ·
        refine ⟨51782685347929728095553101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138087160927812608254808269 51782685347929728095553101)
        ·
          refine ⟨19418507005473648035832413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51782685347929728095553101 19418507005473648035832413)
          ·
            refine ⟨7281940127052618013437155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19418507005473648035832413 7281940127052618013437155)
            ·
              refine ⟨10922910190578927020155733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7281940127052618013437155 10922910190578927020155733)
              ·
                refine ⟨64001426897923400508725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10922910190578927020155733 64001426897923400508725)
                ·
                  rfl

theorem cell23_3365343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 9].length) (baseStart_3365343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365343 prefixEnd_3365343 := by exact prefixLift 3365343
  have htrace : WordTrace (prefixWord ++ tailWord_3365343) baseStart_3365343 baseEnd_3365343 := by
    simpa [prefixWord, tailWord_3365343, baseEnd_3365343] using wordTrace_append hprefix tailTrace_3365343
  have hstable : (prefixWord ++ tailWord_3365343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365343).length < 2 ^ (prefixWord ++ tailWord_3365343).sum := by decide
  have hdescent : baseEnd_3365343 < baseStart_3365343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365357 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 5]
def baseStart_3365357 : Nat := 118140960795 + 3365357 * 2 ^ 59
def prefixEnd_3365357 : Nat := 4983230072969 + 3 ^ 40 * 3365357 * 2
def baseEnd_3365357 : Nat := 1728045714973094758960511

theorem tailTrace_3365357 : CollatzResearch.WordTrace tailWord_3365357 prefixEnd_3365357 1728045714973094758960511 := by
  unfold tailWord_3365357
  simp only [CollatzResearch.WordTrace]
  refine ⟨122744653668893821061950325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81829769112595880707966883 122744653668893821061950325)
  ·
    refine ⟨11507311281458795724557843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122744653668893821061950325 11507311281458795724557843)
    ·
      refine ⟨17260966922188193586836765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11507311281458795724557843 17260966922188193586836765)
      ·
        refine ⟨6472862595820572595063787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17260966922188193586836765 6472862595820572595063787)
        ·
          refine ⟨9709293893730858892595681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472862595820572595063787 9709293893730858892595681)
          ·
            refine ⟨7281970420298144169446761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9709293893730858892595681 7281970420298144169446761)
            ·
              refine ⟨5461477815223608127085071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7281970420298144169446761 5461477815223608127085071)
              ·
                refine ⟨8192216722835412190627607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461477815223608127085071 8192216722835412190627607)
                ·
                  refine ⟨12288325084253118285941411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8192216722835412190627607 12288325084253118285941411)
                  ·
                    refine ⟨18432487626379677428912117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12288325084253118285941411 18432487626379677428912117)
                    ·
                      refine ⟨1728045714973094758960511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18432487626379677428912117 1728045714973094758960511)
                      ·
                        rfl

theorem cell23_3365357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_3365357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365357 prefixEnd_3365357 := by exact prefixLift 3365357
  have htrace : WordTrace (prefixWord ++ tailWord_3365357) baseStart_3365357 baseEnd_3365357 := by
    simpa [prefixWord, tailWord_3365357, baseEnd_3365357] using wordTrace_append hprefix tailTrace_3365357
  have hstable : (prefixWord ++ tailWord_3365357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365357).length < 2 ^ (prefixWord ++ tailWord_3365357).sum := by decide
  have hdescent : baseEnd_3365357 < baseStart_3365357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365373 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_3365373 : Nat := 118140960795 + 3365373 * 2 ^ 59
def prefixEnd_3365373 : Nat := 4983230072969 + 3 ^ 40 * 3365373 * 2
def baseEnd_3365373 : Nat := 576017976887855565453479

theorem tailTrace_3365373 : CollatzResearch.WordTrace tailWord_3365373 prefixEnd_3365373 576017976887855565453479 := by
  unfold tailWord_3365373
  simp only [CollatzResearch.WordTrace]
  refine ⟨122745237236835855794532773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81830158157890570529688515 122745237236835855794532773)
  ·
    refine ⟨23014731981906722961474895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122745237236835855794532773 23014731981906722961474895)
    ·
      refine ⟨34522097972860084442212343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014731981906722961474895 34522097972860084442212343)
      ·
        refine ⟨51783146959290126663318515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34522097972860084442212343 51783146959290126663318515)
        ·
          refine ⟨77674720438935189994977773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51783146959290126663318515 77674720438935189994977773)
          ·
            refine ⟨29128020164600696248116665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77674720438935189994977773 29128020164600696248116665)
            ·
              refine ⟨21846015123450522186087499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29128020164600696248116665 21846015123450522186087499)
              ·
                refine ⟨32769022685175783279131249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21846015123450522186087499 32769022685175783279131249)
                ·
                  refine ⟨24576767013881837459348437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32769022685175783279131249 24576767013881837459348437)
                  ·
                    refine ⟨576017976887855565453479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24576767013881837459348437 576017976887855565453479)
                    ·
                      rfl

theorem cell23_3365373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_3365373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365373 prefixEnd_3365373 := by exact prefixLift 3365373
  have htrace : WordTrace (prefixWord ++ tailWord_3365373) baseStart_3365373 baseEnd_3365373 := by
    simpa [prefixWord, tailWord_3365373, baseEnd_3365373] using wordTrace_append hprefix tailTrace_3365373
  have hstable : (prefixWord ++ tailWord_3365373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365373).length < 2 ^ (prefixWord ++ tailWord_3365373).sum := by decide
  have hdescent : baseEnd_3365373 < baseStart_3365373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365393 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 4]
def baseStart_3365393 : Nat := 118140960795 + 3365393 * 2 ^ 59
def prefixEnd_3365393 : Nat := 4983230072969 + 3 ^ 40 * 3365393 * 2
def baseEnd_3365393 : Nat := 1728064200276656618110345

theorem tailTrace_3365393 : CollatzResearch.WordTrace tailWord_3365393 prefixEnd_3365393 1728064200276656618110345 := by
  unfold tailWord_3365393
  simp only [CollatzResearch.WordTrace]
  refine ⟨122745966696763399210260833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81830644464508932806840555 122745966696763399210260833)
  ·
    refine ⟨92059475022572549407695625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122745966696763399210260833 92059475022572549407695625)
    ·
      refine ⟨69044606266929412055771719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92059475022572549407695625 69044606266929412055771719)
      ·
        refine ⟨103566909400394118083657579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69044606266929412055771719 103566909400394118083657579)
        ·
          refine ⟨155350364100591177125486369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103566909400394118083657579 155350364100591177125486369)
          ·
            refine ⟨116512773075443382844114777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155350364100591177125486369 116512773075443382844114777)
            ·
              refine ⟨87384579806582537133086083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116512773075443382844114777 87384579806582537133086083)
              ·
                refine ⟨131076869709873805699629125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87384579806582537133086083 131076869709873805699629125)
                ·
                  refine ⟨24576913070601338568680461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131076869709873805699629125 24576913070601338568680461)
                  ·
                    refine ⟨9216342401475501963255173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24576913070601338568680461 9216342401475501963255173)
                    ·
                      refine ⟨1728064200276656618110345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9216342401475501963255173 1728064200276656618110345)
                      ·
                        rfl

theorem cell23_3365393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 4].length) (baseStart_3365393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365393 prefixEnd_3365393 := by exact prefixLift 3365393
  have htrace : WordTrace (prefixWord ++ tailWord_3365393) baseStart_3365393 baseEnd_3365393 := by
    simpa [prefixWord, tailWord_3365393, baseEnd_3365393] using wordTrace_append hprefix tailTrace_3365393
  have hstable : (prefixWord ++ tailWord_3365393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365393).length < 2 ^ (prefixWord ++ tailWord_3365393).sum := by decide
  have hdescent : baseEnd_3365393 < baseStart_3365393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365397 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 3, 3, 2]
def baseStart_3365397 : Nat := 118140960795 + 3365397 * 2 ^ 59
def prefixEnd_3365397 : Nat := 4983230072969 + 3 ^ 40 * 3365397 * 2
def baseEnd_3365397 : Nat := 1728066254199274602460327

theorem tailTrace_3365397 : CollatzResearch.WordTrace tailWord_3365397 prefixEnd_3365397 1728066254199274602460327 := by
  unfold tailWord_3365397
  simp only [CollatzResearch.WordTrace]
  refine ⟨122746112588748907893406445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81830741725832605262270963 122746112588748907893406445)
  ·
    refine ⟨46029792220780840460027417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122746112588748907893406445 46029792220780840460027417)
    ·
      refine ⟨34522344165585630345020563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46029792220780840460027417 34522344165585630345020563)
      ·
        refine ⟨51783516248378445517530845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34522344165585630345020563 51783516248378445517530845)
        ·
          refine ⟨19418818593141917069074067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51783516248378445517530845 19418818593141917069074067)
          ·
            refine ⟨29128227889712875603611101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19418818593141917069074067 29128227889712875603611101)
            ·
              refine ⟨10923085458642328351354163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29128227889712875603611101 10923085458642328351354163)
              ·
                refine ⟨16384628187963492527031245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10923085458642328351354163 16384628187963492527031245)
                ·
                  refine ⟨6144235570486309697636717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16384628187963492527031245 6144235570486309697636717)
                  ·
                    refine ⟨2304088338932366136613769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6144235570486309697636717 2304088338932366136613769)
                    ·
                      refine ⟨1728066254199274602460327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304088338932366136613769 1728066254199274602460327)
                      ·
                        rfl

theorem cell23_3365397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 3, 2].length) (baseStart_3365397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365397 prefixEnd_3365397 := by exact prefixLift 3365397
  have htrace : WordTrace (prefixWord ++ tailWord_3365397) baseStart_3365397 baseEnd_3365397 := by
    simpa [prefixWord, tailWord_3365397, baseEnd_3365397] using wordTrace_append hprefix tailTrace_3365397
  have hstable : (prefixWord ++ tailWord_3365397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365397).length < 2 ^ (prefixWord ++ tailWord_3365397).sum := by decide
  have hdescent : baseEnd_3365397 < baseStart_3365397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365422 : List Nat := [4, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2]
def baseStart_3365422 : Nat := 118140960795 + 3365422 * 2 ^ 59
def prefixEnd_3365422 : Nat := 4983230072969 + 3 ^ 40 * 3365422 * 2
def baseEnd_3365422 : Nat := 1728079091215637004647713

theorem tailTrace_3365422 : CollatzResearch.WordTrace tailWord_3365422 prefixEnd_3365422 1728079091215637004647713 := by
  unfold tailWord_3365422
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343378051707292145383315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81831349609105558108711013 15343378051707292145383315)
  ·
    refine ⟨23015067077560938218074973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15343378051707292145383315 23015067077560938218074973)
    ·
      refine ⟨8630650154085351831778115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23015067077560938218074973 8630650154085351831778115)
      ·
        refine ⟨12945975231128027747667173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8630650154085351831778115 12945975231128027747667173)
        ·
          refine ⟨2427370355836505202687595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12945975231128027747667173 2427370355836505202687595)
          ·
            refine ⟨3641055533754757804031393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427370355836505202687595 3641055533754757804031393)
            ·
              refine ⟨2730791650316068353023545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641055533754757804031393 2730791650316068353023545)
              ·
                refine ⟨2048093737737051264767659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2730791650316068353023545 2048093737737051264767659)
                ·
                  refine ⟨3072140606605576897151489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048093737737051264767659 3072140606605576897151489)
                  ·
                    refine ⟨2304105454954182672863617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072140606605576897151489 2304105454954182672863617)
                    ·
                      refine ⟨1728079091215637004647713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304105454954182672863617 1728079091215637004647713)
                      ·
                        rfl

theorem cell23_3365422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_3365422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365422 prefixEnd_3365422 := by exact prefixLift 3365422
  have htrace : WordTrace (prefixWord ++ tailWord_3365422) baseStart_3365422 baseEnd_3365422 := by
    simpa [prefixWord, tailWord_3365422, baseEnd_3365422] using wordTrace_append hprefix tailTrace_3365422
  have hstable : (prefixWord ++ tailWord_3365422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365422).length < 2 ^ (prefixWord ++ tailWord_3365422).sum := by decide
  have hdescent : baseEnd_3365422 < baseStart_3365422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365423 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4]
def baseStart_3365423 : Nat := 118140960795 + 3365423 * 2 ^ 59
def prefixEnd_3365423 : Nat := 4983230072969 + 3 ^ 40 * 3365423 * 2
def baseEnd_3365423 : Nat := 1728079604696291500735207

theorem tailTrace_3365423 : CollatzResearch.WordTrace tailWord_3365423 prefixEnd_3365423 1728079604696291500735207 := by
  unfold tailWord_3365423
  simp only [CollatzResearch.WordTrace]
  refine ⟨122747060886654714333852923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81831373924436476222568615 122747060886654714333852923)
  ·
    refine ⟨184120591329982071500779385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122747060886654714333852923 184120591329982071500779385)
    ·
      refine ⟨138090443497486553625584539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184120591329982071500779385 138090443497486553625584539)
      ·
        refine ⟨207135665246229830438376809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138090443497486553625584539 207135665246229830438376809)
        ·
          refine ⟨155351748934672372828782607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207135665246229830438376809 155351748934672372828782607)
          ·
            refine ⟨233027623402008559243173911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155351748934672372828782607 233027623402008559243173911)
            ·
              refine ⟨349541435103012838864760867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233027623402008559243173911 349541435103012838864760867)
              ·
                refine ⟨524312152654519258297141301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349541435103012838864760867 524312152654519258297141301)
                ·
                  refine ⟨49154264311361180465356997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 524312152654519258297141301 49154264311361180465356997)
                  ·
                    refine ⟨9216424558380221337254437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49154264311361180465356997 9216424558380221337254437)
                    ·
                      refine ⟨1728079604696291500735207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9216424558380221337254437 1728079604696291500735207)
                      ·
                        rfl

theorem cell23_3365423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 4].length) (baseStart_3365423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365423 prefixEnd_3365423 := by exact prefixLift 3365423
  have htrace : WordTrace (prefixWord ++ tailWord_3365423) baseStart_3365423 baseEnd_3365423 := by
    simpa [prefixWord, tailWord_3365423, baseEnd_3365423] using wordTrace_append hprefix tailTrace_3365423
  have hstable : (prefixWord ++ tailWord_3365423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365423).length < 2 ^ (prefixWord ++ tailWord_3365423).sum := by decide
  have hdescent : baseEnd_3365423 < baseStart_3365423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365450 : List Nat := [3, 1, 2, 1, 1, 5, 1, 2, 7]
def baseStart_3365450 : Nat := 118140960795 + 3365450 * 2 ^ 59
def prefixEnd_3365450 : Nat := 4983230072969 + 3 ^ 40 * 3365450 * 2
def baseEnd_3365450 : Nat := 192010385408218099455287

theorem tailTrace_3365450 : CollatzResearch.WordTrace tailWord_3365450 prefixEnd_3365450 192010385408218099455287 := by
  unfold tailWord_3365450
  simp only [CollatzResearch.WordTrace]
  refine ⟨30687011414389224486271451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81832030438371265296723869 30687011414389224486271451)
  ·
    refine ⟨46030517121583836729407177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30687011414389224486271451 46030517121583836729407177)
    ·
      refine ⟨34522887841187877547055383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46030517121583836729407177 34522887841187877547055383)
      ·
        refine ⟨51784331761781816320583075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34522887841187877547055383 51784331761781816320583075)
        ·
          refine ⟨77676497642672724480874613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51784331761781816320583075 77676497642672724480874613)
          ·
            refine ⟨7282171654000567920081995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77676497642672724480874613 7282171654000567920081995)
            ·
              refine ⟨10923257481000851880122993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282171654000567920081995 10923257481000851880122993)
              ·
                refine ⟨8192443110750638910092245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923257481000851880122993 8192443110750638910092245)
                ·
                  refine ⟨192010385408218099455287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8192443110750638910092245 192010385408218099455287)
                  ·
                    rfl

theorem cell23_3365450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 2, 7].length) (baseStart_3365450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365450 prefixEnd_3365450 := by exact prefixLift 3365450
  have htrace : WordTrace (prefixWord ++ tailWord_3365450) baseStart_3365450 baseEnd_3365450 := by
    simpa [prefixWord, tailWord_3365450, baseEnd_3365450] using wordTrace_append hprefix tailTrace_3365450
  have hstable : (prefixWord ++ tailWord_3365450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365450).length < 2 ^ (prefixWord ++ tailWord_3365450).sum := by decide
  have hdescent : baseEnd_3365450 < baseStart_3365450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365500 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_3365500 : Nat := 118140960795 + 3365500 * 2 ^ 59
def prefixEnd_3365500 : Nat := 4983230072969 + 3 ^ 40 * 3365500 * 2
def baseEnd_3365500 : Nat := 1728119142706687699472353

theorem tailTrace_3365500 : CollatzResearch.WordTrace tailWord_3365500 prefixEnd_3365500 1728119142706687699472353 := by
  unfold tailWord_3365500
  simp only [CollatzResearch.WordTrace]
  refine ⟨61374934653687878242202977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81833246204917170989603969 61374934653687878242202977)
  ·
    refine ⟨46031200990265908681652233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61374934653687878242202977 46031200990265908681652233)
    ·
      refine ⟨34523400742699431511239175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46031200990265908681652233 34523400742699431511239175)
      ·
        refine ⟨51785101114049147266858763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34523400742699431511239175 51785101114049147266858763)
        ·
          refine ⟨77677651671073720900288145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51785101114049147266858763 77677651671073720900288145)
          ·
            refine ⟨58258238753305290675216109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77677651671073720900288145 58258238753305290675216109)
            ·
              refine ⟨21846839532489484003206041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58258238753305290675216109 21846839532489484003206041)
              ·
                refine ⟨16385129649367113002404531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21846839532489484003206041 16385129649367113002404531)
                ·
                  refine ⟨24577694474050669503606797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16385129649367113002404531 24577694474050669503606797)
                  ·
                    refine ⟨9216635427769001063852549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24577694474050669503606797 9216635427769001063852549)
                    ·
                      refine ⟨1728119142706687699472353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9216635427769001063852549 1728119142706687699472353)
                      ·
                        rfl

theorem cell23_3365500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_3365500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365500 prefixEnd_3365500 := by exact prefixLift 3365500
  have htrace : WordTrace (prefixWord ++ tailWord_3365500) baseStart_3365500 baseEnd_3365500 := by
    simpa [prefixWord, tailWord_3365500, baseEnd_3365500] using wordTrace_append hprefix tailTrace_3365500
  have hstable : (prefixWord ++ tailWord_3365500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365500).length < 2 ^ (prefixWord ++ tailWord_3365500).sum := by decide
  have hdescent : baseEnd_3365500 < baseStart_3365500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365534 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_3365534 : Nat := 118140960795 + 3365534 * 2 ^ 59
def prefixEnd_3365534 : Nat := 4983230072969 + 3 ^ 40 * 3365534 * 2
def baseEnd_3365534 : Nat := 1728136601048940566447197

theorem tailTrace_3365534 : CollatzResearch.WordTrace tailWord_3365534 prefixEnd_3365534 1728136601048940566447197 := by
  unfold tailWord_3365534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15343888673656572536392957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81834072926168386860762437 15343888673656572536392957)
  ·
    refine ⟨5753958252621214701147359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15343888673656572536392957 5753958252621214701147359)
    ·
      refine ⟨8630937378931822051721039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5753958252621214701147359 8630937378931822051721039)
      ·
        refine ⟨12946406068397733077581559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8630937378931822051721039 12946406068397733077581559)
        ·
          refine ⟨19419609102596599616372339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946406068397733077581559 19419609102596599616372339)
          ·
            refine ⟨29129413653894899424558509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19419609102596599616372339 29129413653894899424558509)
            ·
              refine ⟨10923530120210587284209441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29129413653894899424558509 10923530120210587284209441)
              ·
                refine ⟨8192647590157940463157081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923530120210587284209441 8192647590157940463157081)
                ·
                  refine ⟨6144485692618455347367811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8192647590157940463157081 6144485692618455347367811)
                  ·
                    refine ⟨9216728538927683021051717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6144485692618455347367811 9216728538927683021051717)
                    ·
                      refine ⟨1728136601048940566447197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9216728538927683021051717 1728136601048940566447197)
                      ·
                        rfl

theorem cell23_3365534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_3365534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365534 prefixEnd_3365534 := by exact prefixLift 3365534
  have htrace : WordTrace (prefixWord ++ tailWord_3365534) baseStart_3365534 baseEnd_3365534 := by
    simpa [prefixWord, tailWord_3365534, baseEnd_3365534] using wordTrace_append hprefix tailTrace_3365534
  have hstable : (prefixWord ++ tailWord_3365534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365534).length < 2 ^ (prefixWord ++ tailWord_3365534).sum := by decide
  have hdescent : baseEnd_3365534 < baseStart_3365534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365540 : List Nat := [2, 3, 1, 2, 2, 1, 1, 3, 8]
def baseStart_3365540 : Nat := 118140960795 + 3365540 * 2 ^ 59
def prefixEnd_3365540 : Nat := 4983230072969 + 3 ^ 40 * 3365540 * 2
def baseEnd_3365540 : Nat := 192015520214763060330241

theorem tailTrace_3365540 : CollatzResearch.WordTrace tailWord_3365540 prefixEnd_3365540 192015520214763060330241 := by
  unfold tailWord_3365540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61375664113615421657931037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81834218818153895543908049 61375664113615421657931037)
  ·
    refine ⟨23015874042605783121724139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61375664113615421657931037 23015874042605783121724139)
    ·
      refine ⟨34523811063908674682586209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23015874042605783121724139 34523811063908674682586209)
      ·
        refine ⟨25892858297931506011939657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34523811063908674682586209 25892858297931506011939657)
        ·
          refine ⟨19419643723448629508954743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25892858297931506011939657 19419643723448629508954743)
          ·
            refine ⟨29129465585172944263432115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19419643723448629508954743 29129465585172944263432115)
            ·
              refine ⟨43694198377759416395148173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29129465585172944263432115 43694198377759416395148173)
              ·
                refine ⟨16385324391659781148180565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43694198377759416395148173 16385324391659781148180565)
                ·
                  refine ⟨192015520214763060330241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16385324391659781148180565 192015520214763060330241)
                  ·
                    rfl

theorem cell23_3365540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_3365540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365540 prefixEnd_3365540 := by exact prefixLift 3365540
  have htrace : WordTrace (prefixWord ++ tailWord_3365540) baseStart_3365540 baseEnd_3365540 := by
    simpa [prefixWord, tailWord_3365540, baseEnd_3365540] using wordTrace_append hprefix tailTrace_3365540
  have hstable : (prefixWord ++ tailWord_3365540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365540).length < 2 ^ (prefixWord ++ tailWord_3365540).sum := by decide
  have hdescent : baseEnd_3365540 < baseStart_3365540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365594 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2]
def baseStart_3365594 : Nat := 118140960795 + 3365594 * 2 ^ 59
def prefixEnd_3365594 : Nat := 4983230072969 + 3 ^ 40 * 3365594 * 2
def baseEnd_3365594 : Nat := 1728167409888210331696921

theorem tailTrace_3365594 : CollatzResearch.WordTrace tailWord_3365594 prefixEnd_3365594 1728167409888210331696921 := by
  unfold tailWord_3365594
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688324442258802634581959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81835531846023473692218557 30688324442258802634581959)
  ·
    refine ⟨46032486663388203951872939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688324442258802634581959 46032486663388203951872939)
    ·
      refine ⟨69048729995082305927809409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46032486663388203951872939 69048729995082305927809409)
      ·
        refine ⟨51786547496311729445857057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69048729995082305927809409 51786547496311729445857057)
        ·
          refine ⟨38839910622233797084392793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51786547496311729445857057 38839910622233797084392793)
          ·
            refine ⟨29129932966675347813294595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38839910622233797084392793 29129932966675347813294595)
            ·
              refine ⟨43694899450013021719941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29129932966675347813294595 43694899450013021719941893)
              ·
                refine ⟨8192793646877441572489105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43694899450013021719941893 8192793646877441572489105)
                ·
                  refine ⟨6144595235158081179366829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8192793646877441572489105 6144595235158081179366829)
                  ·
                    refine ⟨2304223213184280442262561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6144595235158081179366829 2304223213184280442262561)
                    ·
                      refine ⟨1728167409888210331696921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304223213184280442262561 1728167409888210331696921)
                      ·
                        rfl

theorem cell23_3365594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_3365594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365594 prefixEnd_3365594 := by exact prefixLift 3365594
  have htrace : WordTrace (prefixWord ++ tailWord_3365594) baseStart_3365594 baseEnd_3365594 := by
    simpa [prefixWord, tailWord_3365594, baseEnd_3365594] using wordTrace_append hprefix tailTrace_3365594
  have hstable : (prefixWord ++ tailWord_3365594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365594).length < 2 ^ (prefixWord ++ tailWord_3365594).sum := by decide
  have hdescent : baseEnd_3365594 < baseStart_3365594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365600 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_3365600 : Nat := 118140960795 + 3365600 * 2 ^ 59
def prefixEnd_3365600 : Nat := 4983230072969 + 3 ^ 40 * 3365600 * 2
def baseEnd_3365600 : Nat := 576056830257379102740631

theorem tailTrace_3365600 : CollatzResearch.WordTrace tailWord_3365600 prefixEnd_3365600 576056830257379102740631 := by
  unfold tailWord_3365600
  simp only [CollatzResearch.WordTrace]
  refine ⟨61376758303506736781523127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81835677738008982375364169 61376758303506736781523127)
  ·
    refine ⟨92065137455260105172284691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61376758303506736781523127 92065137455260105172284691)
    ·
      refine ⟨138097706182890157758427037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92065137455260105172284691 138097706182890157758427037)
      ·
        refine ⟨51786639818583809159410139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138097706182890157758427037 51786639818583809159410139)
        ·
          refine ⟨77679959727875713739115209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51786639818583809159410139 77679959727875713739115209)
          ·
            refine ⟨58259969795906785304336407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77679959727875713739115209 58259969795906785304336407)
            ·
              refine ⟨87389954693860177956504611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58259969795906785304336407 87389954693860177956504611)
              ·
                refine ⟨131084932040790266934756917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87389954693860177956504611 131084932040790266934756917)
                ·
                  refine ⟨12289212378824087525133461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131084932040790266934756917 12289212378824087525133461)
                  ·
                    refine ⟨576056830257379102740631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12289212378824087525133461 576056830257379102740631)
                    ·
                      rfl

theorem cell23_3365600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_3365600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365600 prefixEnd_3365600 := by exact prefixLift 3365600
  have htrace : WordTrace (prefixWord ++ tailWord_3365600) baseStart_3365600 baseEnd_3365600 := by
    simpa [prefixWord, tailWord_3365600, baseEnd_3365600] using wordTrace_append hprefix tailTrace_3365600
  have hstable : (prefixWord ++ tailWord_3365600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365600).length < 2 ^ (prefixWord ++ tailWord_3365600).sum := by decide
  have hdescent : baseEnd_3365600 < baseStart_3365600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365617 : List Nat := [1, 2, 2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_3365617 : Nat := 118140960795 + 3365617 * 2 ^ 59
def prefixEnd_3365617 : Nat := 4983230072969 + 3 ^ 40 * 3365617 * 2
def baseEnd_3365617 : Nat := 576059739981087913903105

theorem tailTrace_3365617 : CollatzResearch.WordTrace tailWord_3365617 prefixEnd_3365617 576059739981087913903105 := by
  unfold tailWord_3365617
  simp only [CollatzResearch.WordTrace]
  refine ⟨122754136647951885466415105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81836091098634590310943403 122754136647951885466415105)
  ·
    refine ⟨92065602485963914099811329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122754136647951885466415105 92065602485963914099811329)
    ·
      refine ⟨69049201864472935574858497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92065602485963914099811329 69049201864472935574858497)
      ·
        refine ⟨51786901398354701681143873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69049201864472935574858497 51786901398354701681143873)
        ·
          refine ⟨38840176048766026260857905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51786901398354701681143873 38840176048766026260857905)
          ·
            refine ⟨29130132036574519695643429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38840176048766026260857905 29130132036574519695643429)
            ·
              refine ⟨5461899756857722442933143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29130132036574519695643429 5461899756857722442933143)
              ·
                refine ⟨8192849635286583664399715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5461899756857722442933143 8192849635286583664399715)
                ·
                  refine ⟨12289274452929875496599573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8192849635286583664399715 12289274452929875496599573)
                  ·
                    refine ⟨576059739981087913903105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12289274452929875496599573 576059739981087913903105)
                    ·
                      rfl

theorem cell23_3365617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_3365617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365617 prefixEnd_3365617 := by exact prefixLift 3365617
  have htrace : WordTrace (prefixWord ++ tailWord_3365617) baseStart_3365617 baseEnd_3365617 := by
    simpa [prefixWord, tailWord_3365617, baseEnd_3365617] using wordTrace_append hprefix tailTrace_3365617
  have hstable : (prefixWord ++ tailWord_3365617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365617).length < 2 ^ (prefixWord ++ tailWord_3365617).sum := by decide
  have hdescent : baseEnd_3365617 < baseStart_3365617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365634 : List Nat := [3, 4, 1, 1, 1, 2, 2, 2, 1, 6]
def baseStart_3365634 : Nat := 118140960795 + 3365634 * 2 ^ 59
def prefixEnd_3365634 : Nat := 4983230072969 + 3 ^ 40 * 3365634 * 2
def baseEnd_3365634 : Nat := 576062649704796725065579

theorem tailTrace_3365634 : CollatzResearch.WordTrace tailWord_3365634 prefixEnd_3365634 576062649704796725065579 := by
  unfold tailWord_3365634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688689172222574342445989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81836504459260198246522637 30688689172222574342445989)
  ·
    refine ⟨5754129219791732689208623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30688689172222574342445989 5754129219791732689208623)
    ·
      refine ⟨8631193829687599033812935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754129219791732689208623 8631193829687599033812935)
      ·
        refine ⟨12946790744531398550719403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8631193829687599033812935 12946790744531398550719403)
        ·
          refine ⟨19420186116797097826079105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12946790744531398550719403 19420186116797097826079105)
          ·
            refine ⟨14565139587597823369559329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19420186116797097826079105 14565139587597823369559329)
            ·
              refine ⟨10923854690698367527169497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14565139587597823369559329 10923854690698367527169497)
              ·
                refine ⟨8192891018023775645377123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923854690698367527169497 8192891018023775645377123)
                ·
                  refine ⟨12289336527035663468065685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8192891018023775645377123 12289336527035663468065685)
                  ·
                    refine ⟨576062649704796725065579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12289336527035663468065685 576062649704796725065579)
                    ·
                      rfl

theorem cell23_3365634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_3365634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365634 prefixEnd_3365634 := by exact prefixLift 3365634
  have htrace : WordTrace (prefixWord ++ tailWord_3365634) baseStart_3365634 baseEnd_3365634 := by
    simpa [prefixWord, tailWord_3365634, baseEnd_3365634] using wordTrace_append hprefix tailTrace_3365634
  have hstable : (prefixWord ++ tailWord_3365634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365634).length < 2 ^ (prefixWord ++ tailWord_3365634).sum := by decide
  have hdescent : baseEnd_3365634 < baseStart_3365634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365658 : List Nat := [3, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2]
def baseStart_3365658 : Nat := 118140960795 + 3365658 * 2 ^ 59
def prefixEnd_3365658 : Nat := 4983230072969 + 3 ^ 40 * 3365658 * 2
def baseEnd_3365658 : Nat := 1728200272650098081296627

theorem tailTrace_3365658 : CollatzResearch.WordTrace tailWord_3365658 prefixEnd_3365658 1728200272650098081296627 := by
  unfold tailWord_3365658
  simp only [CollatzResearch.WordTrace]
  refine ⟨30688908010200837367164407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81837088027202232979105085 30688908010200837367164407)
  ·
    refine ⟨46033362015301256050746611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30688908010200837367164407 46033362015301256050746611)
    ·
      refine ⟨69050043022951884076119917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46033362015301256050746611 69050043022951884076119917)
      ·
        refine ⟨25893766133606956528544969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69050043022951884076119917 25893766133606956528544969)
        ·
          refine ⟨19420324600205217396408727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25893766133606956528544969 19420324600205217396408727)
          ·
            refine ⟨29130486900307826094613091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19420324600205217396408727 29130486900307826094613091)
            ·
              refine ⟨43695730350461739141919637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29130486900307826094613091 43695730350461739141919637)
              ·
                refine ⟨2048237360177894022277483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43695730350461739141919637 2048237360177894022277483)
                ·
                  refine ⟨3072356040266841033416225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048237360177894022277483 3072356040266841033416225)
                  ·
                    refine ⟨2304267030200130775062169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072356040266841033416225 2304267030200130775062169)
                    ·
                      refine ⟨1728200272650098081296627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304267030200130775062169 1728200272650098081296627)
                      ·
                        rfl

theorem cell23_3365658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_3365658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365658 prefixEnd_3365658 := by exact prefixLift 3365658
  have htrace : WordTrace (prefixWord ++ tailWord_3365658) baseStart_3365658 baseEnd_3365658 := by
    simpa [prefixWord, tailWord_3365658, baseEnd_3365658] using wordTrace_append hprefix tailTrace_3365658
  have hstable : (prefixWord ++ tailWord_3365658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365658).length < 2 ^ (prefixWord ++ tailWord_3365658).sum := by decide
  have hdescent : baseEnd_3365658 < baseStart_3365658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365661 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 5]
def baseStart_3365661 : Nat := 118140960795 + 3365661 * 2 ^ 59
def prefixEnd_3365661 : Nat := 4983230072969 + 3 ^ 40 * 3365661 * 2
def baseEnd_3365661 : Nat := 1728201813092061569559113

theorem tailTrace_3365661 : CollatzResearch.WordTrace tailWord_3365661 prefixEnd_3365661 1728201813092061569559113 := by
  unfold tailWord_3365661
  simp only [CollatzResearch.WordTrace]
  refine ⟨122755741459792480981016837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81837160973194987320677891 122755741459792480981016837)
  ·
    refine ⟨23016701523711090183940657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122755741459792480981016837 23016701523711090183940657)
    ·
      refine ⟨17262526142783317637955493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23016701523711090183940657 17262526142783317637955493)
      ·
        refine ⟨3236723651771872057116655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17262526142783317637955493 3236723651771872057116655)
        ·
          refine ⟨4855085477657808085674983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236723651771872057116655 4855085477657808085674983)
          ·
            refine ⟨7282628216486712128512475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855085477657808085674983 7282628216486712128512475)
            ·
              refine ⟨10923942324730068192768713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7282628216486712128512475 10923942324730068192768713)
              ·
                refine ⟨8192956743547551144576535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10923942324730068192768713 8192956743547551144576535)
                ·
                  refine ⟨12289435115321326716864803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8192956743547551144576535 12289435115321326716864803)
                  ·
                    refine ⟨18434152672981990075297205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12289435115321326716864803 18434152672981990075297205)
                    ·
                      refine ⟨1728201813092061569559113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18434152672981990075297205 1728201813092061569559113)
                      ·
                        rfl

theorem cell23_3365661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_3365661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365661 prefixEnd_3365661 := by exact prefixLift 3365661
  have htrace : WordTrace (prefixWord ++ tailWord_3365661) baseStart_3365661 baseEnd_3365661 := by
    simpa [prefixWord, tailWord_3365661, baseEnd_3365661] using wordTrace_append hprefix tailTrace_3365661
  have hstable : (prefixWord ++ tailWord_3365661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365661).length < 2 ^ (prefixWord ++ tailWord_3365661).sum := by decide
  have hdescent : baseEnd_3365661 < baseStart_3365661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365668 : List Nat := [2, 3, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_3365668 : Nat := 118140960795 + 3365668 * 2 ^ 59
def prefixEnd_3365668 : Nat := 4983230072969 + 3 ^ 40 * 3365668 * 2
def baseEnd_3365668 : Nat := 576068469152214347390527

theorem tailTrace_3365668 : CollatzResearch.WordTrace tailWord_3365668 prefixEnd_3365668 576068469152214347390527 := by
  unfold tailWord_3365668
  simp only [CollatzResearch.WordTrace]
  refine ⟨61377998385383560588260829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81837331180511414117681105 61377998385383560588260829)
  ·
    refine ⟨23016749394518835220597811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61377998385383560588260829 23016749394518835220597811)
    ·
      refine ⟨34525124091778252830896717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23016749394518835220597811 34525124091778252830896717)
      ·
        refine ⟨12946921534416844811586269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34525124091778252830896717 12946921534416844811586269)
        ·
          refine ⟨4855095575406316804344851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12946921534416844811586269 4855095575406316804344851)
          ·
            refine ⟨7282643363109475206517277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855095575406316804344851 7282643363109475206517277)
            ·
              refine ⟨2730991261166053202443979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7282643363109475206517277 2730991261166053202443979)
              ·
                refine ⟨4096486891749079803665969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730991261166053202443979 4096486891749079803665969)
                ·
                  refine ⟨3072365168811809852749477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4096486891749079803665969 3072365168811809852749477)
                  ·
                    refine ⟨576068469152214347390527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072365168811809852749477 576068469152214347390527)
                    ·
                      rfl

theorem cell23_3365668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_3365668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365668 prefixEnd_3365668 := by exact prefixLift 3365668
  have htrace : WordTrace (prefixWord ++ tailWord_3365668) baseStart_3365668 baseEnd_3365668 := by
    simpa [prefixWord, tailWord_3365668, baseEnd_3365668] using wordTrace_append hprefix tailTrace_3365668
  have hstable : (prefixWord ++ tailWord_3365668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365668).length < 2 ^ (prefixWord ++ tailWord_3365668).sum := by decide
  have hdescent : baseEnd_3365668 < baseStart_3365668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365678 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3365678 : Nat := 118140960795 + 3365678 * 2 ^ 59
def prefixEnd_3365678 : Nat := 4983230072969 + 3 ^ 40 * 3365678 * 2
def baseEnd_3365678 : Nat := 1728210542263188003046535

theorem tailTrace_3365678 : CollatzResearch.WordTrace tailWord_3365678 prefixEnd_3365678 1728210542263188003046535 := by
  unfold tailWord_3365678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15344545187591361610548211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81837574333820595256257125 15344545187591361610548211)
  ·
    refine ⟨23016817781387042415822317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15344545187591361610548211 23016817781387042415822317)
    ·
      refine ⟨8631306668020140905933369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23016817781387042415822317 8631306668020140905933369)
      ·
        refine ⟨6473480001015105679450027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631306668020140905933369 6473480001015105679450027)
        ·
          refine ⟨9710220001522658519175041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473480001015105679450027 9710220001522658519175041)
          ·
            refine ⟨7282665001141993889381281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710220001522658519175041 7282665001141993889381281)
            ·
              refine ⟨5461998750856495417035961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282665001141993889381281 5461998750856495417035961)
              ·
                refine ⟨4096499063142371562776971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5461998750856495417035961 4096499063142371562776971)
                ·
                  refine ⟨6144748594713557344165457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4096499063142371562776971 6144748594713557344165457)
                  ·
                    refine ⟨4608561446035168008124093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6144748594713557344165457 4608561446035168008124093)
                    ·
                      refine ⟨1728210542263188003046535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4608561446035168008124093 1728210542263188003046535)
                      ·
                        rfl

theorem cell23_3365678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3365678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365678 prefixEnd_3365678 := by exact prefixLift 3365678
  have htrace : WordTrace (prefixWord ++ tailWord_3365678) baseStart_3365678 baseEnd_3365678 := by
    simpa [prefixWord, tailWord_3365678, baseEnd_3365678] using wordTrace_append hprefix tailTrace_3365678
  have hstable : (prefixWord ++ tailWord_3365678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365678).length < 2 ^ (prefixWord ++ tailWord_3365678).sum := by decide
  have hdescent : baseEnd_3365678 < baseStart_3365678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365709 : List Nat := [1, 6, 1, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_3365709 : Nat := 118140960795 + 3365709 * 2 ^ 59
def prefixEnd_3365709 : Nat := 4983230072969 + 3 ^ 40 * 3365709 * 2
def baseEnd_3365709 : Nat := 1728226460163477381758893

theorem tailTrace_3365709 : CollatzResearch.WordTrace tailWord_3365709 prefixEnd_3365709 1728226460163477381758893 := by
  unfold tailWord_3365709
  simp only [CollatzResearch.WordTrace]
  refine ⟨122757492163618585178764181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81838328109079056785842787 122757492163618585178764181)
  ·
    refine ⟨5754257445169621180254571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122757492163618585178764181 5754257445169621180254571)
    ·
      refine ⟨8631386167754431770381857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5754257445169621180254571 8631386167754431770381857)
      ·
        refine ⟨6473539625815823827786393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8631386167754431770381857 6473539625815823827786393)
        ·
          refine ⟨4855154719361867870839795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6473539625815823827786393 4855154719361867870839795)
          ·
            refine ⟨7282732079042801806259693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855154719361867870839795 7282732079042801806259693)
            ·
              refine ⟨2731024529641050677347385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7282732079042801806259693 2731024529641050677347385)
              ·
                refine ⟨2048268397230788008010539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731024529641050677347385 2048268397230788008010539)
                ·
                  refine ⟨3072402595846182012015809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048268397230788008010539 3072402595846182012015809)
                  ·
                    refine ⟨2304301946884636509011857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072402595846182012015809 2304301946884636509011857)
                    ·
                      refine ⟨1728226460163477381758893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304301946884636509011857 1728226460163477381758893)
                      ·
                        rfl

theorem cell23_3365709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_3365709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365709 prefixEnd_3365709 := by exact prefixLift 3365709
  have htrace : WordTrace (prefixWord ++ tailWord_3365709) baseStart_3365709 baseEnd_3365709 := by
    simpa [prefixWord, tailWord_3365709, baseEnd_3365709] using wordTrace_append hprefix tailTrace_3365709
  have hstable : (prefixWord ++ tailWord_3365709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365709).length < 2 ^ (prefixWord ++ tailWord_3365709).sum := by decide
  have hdescent : baseEnd_3365709 < baseStart_3365709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365717 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3365717 : Nat := 118140960795 + 3365717 * 2 ^ 59
def prefixEnd_3365717 : Nat := 4983230072969 + 3 ^ 40 * 3365717 * 2
def baseEnd_3365717 : Nat := 1728230568008713350458855

theorem tailTrace_3365717 : CollatzResearch.WordTrace tailWord_3365717 prefixEnd_3365717 1728230568008713350458855 := by
  unfold tailWord_3365717
  simp only [CollatzResearch.WordTrace]
  refine ⟨122757783947589602545055405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81838522631726401696703603 122757783947589602545055405)
  ·
    refine ⟨46034168980346100954395777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122757783947589602545055405 46034168980346100954395777)
    ·
      refine ⟨34525626735259575715796833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46034168980346100954395777 34525626735259575715796833)
      ·
        refine ⟨25894220051444681786847625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34525626735259575715796833 25894220051444681786847625)
        ·
          refine ⟨19420665038583511340135719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25894220051444681786847625 19420665038583511340135719)
          ·
            refine ⟨29130997557875267010203579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19420665038583511340135719 29130997557875267010203579)
            ·
              refine ⟨43696496336812900515305369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29130997557875267010203579 43696496336812900515305369)
              ·
                refine ⟨32772372252609675386479027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43696496336812900515305369 32772372252609675386479027)
                ·
                  refine ⟨49158558378914513079718541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32772372252609675386479027 49158558378914513079718541)
                  ·
                    refine ⟨18434459392092942404894453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49158558378914513079718541 18434459392092942404894453)
                    ·
                      refine ⟨1728230568008713350458855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18434459392092942404894453 1728230568008713350458855)
                      ·
                        rfl

theorem cell23_3365717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3365717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365717 prefixEnd_3365717 := by exact prefixLift 3365717
  have htrace : WordTrace (prefixWord ++ tailWord_3365717) baseStart_3365717 baseEnd_3365717 := by
    simpa [prefixWord, tailWord_3365717, baseEnd_3365717] using wordTrace_append hprefix tailTrace_3365717
  have hstable : (prefixWord ++ tailWord_3365717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365717).length < 2 ^ (prefixWord ++ tailWord_3365717).sum := by decide
  have hdescent : baseEnd_3365717 < baseStart_3365717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365727 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4]
def baseStart_3365727 : Nat := 118140960795 + 3365727 * 2 ^ 59
def prefixEnd_3365727 : Nat := 4983230072969 + 3 ^ 40 * 3365727 * 2
def baseEnd_3365727 : Nat := 1728235702815258311333809

theorem tailTrace_3365727 : CollatzResearch.WordTrace tailWord_3365727 prefixEnd_3365727 1728235702815258311333809 := by
  unfold tailWord_3365727
  simp only [CollatzResearch.WordTrace]
  refine ⟨122758148677553374252919435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81838765785035582835279623 122758148677553374252919435)
  ·
    refine ⟨184137223016330061379379153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122758148677553374252919435 184137223016330061379379153)
    ·
      refine ⟨138102917262247546034534365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184137223016330061379379153 138102917262247546034534365)
      ·
        refine ⟨51788593973342829762950387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138102917262247546034534365 51788593973342829762950387)
        ·
          refine ⟨77682890960014244644425581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51788593973342829762950387 77682890960014244644425581)
          ·
            refine ⟨29131084110005341741659593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77682890960014244644425581 29131084110005341741659593)
            ·
              refine ⟨21848313082504006306244695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29131084110005341741659593 21848313082504006306244695)
              ·
                refine ⟨32772469623756009459367043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21848313082504006306244695 32772469623756009459367043)
                ·
                  refine ⟨49158704435634014189050565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32772469623756009459367043 49158704435634014189050565)
                  ·
                    refine ⟨9217257081681377660446981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49158704435634014189050565 9217257081681377660446981)
                    ·
                      refine ⟨1728235702815258311333809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9217257081681377660446981 1728235702815258311333809)
                      ·
                        rfl

theorem cell23_3365727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 4, 4].length) (baseStart_3365727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365727 prefixEnd_3365727 := by exact prefixLift 3365727
  have htrace : WordTrace (prefixWord ++ tailWord_3365727) baseStart_3365727 baseEnd_3365727 := by
    simpa [prefixWord, tailWord_3365727, baseEnd_3365727] using wordTrace_append hprefix tailTrace_3365727
  have hstable : (prefixWord ++ tailWord_3365727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365727).length < 2 ^ (prefixWord ++ tailWord_3365727).sum := by decide
  have hdescent : baseEnd_3365727 < baseStart_3365727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365754 : List Nat := [3, 1, 1, 1, 1, 1, 3, 7, 5]
def baseStart_3365754 : Nat := 118140960795 + 3365754 * 2 ^ 59
def prefixEnd_3365754 : Nat := 4983230072969 + 3 ^ 40 * 3365754 * 2
def baseEnd_3365754 : Nat := 192027729643658856188465

theorem tailTrace_3365754 : CollatzResearch.WordTrace tailWord_3365754 prefixEnd_3365754 192027729643658856188465 := by
  unfold tailWord_3365754
  simp only [CollatzResearch.WordTrace]
  refine ⟨30689783362113889466038079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81839422298970371909434877 30689783362113889466038079)
  ·
    refine ⟨46034675043170834199057119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30689783362113889466038079 46034675043170834199057119)
    ·
      refine ⟨69052012564756251298585679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46034675043170834199057119 69052012564756251298585679)
      ·
        refine ⟨103578018847134376947878519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69052012564756251298585679 103578018847134376947878519)
        ·
          refine ⟨155367028270701565421817779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103578018847134376947878519 155367028270701565421817779)
          ·
            refine ⟨233050542406052348132726669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155367028270701565421817779 233050542406052348132726669)
            ·
              refine ⟨87393953402269630549772501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233050542406052348132726669 87393953402269630549772501)
              ·
                refine ⟨2048295782865694466010293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87393953402269630549772501 2048295782865694466010293)
                ·
                  refine ⟨192027729643658856188465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2048295782865694466010293 192027729643658856188465)
                  ·
                    rfl

theorem cell23_3365754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 7, 5].length) (baseStart_3365754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365754 prefixEnd_3365754 := by exact prefixLift 3365754
  have htrace : WordTrace (prefixWord ++ tailWord_3365754) baseStart_3365754 baseEnd_3365754 := by
    simpa [prefixWord, tailWord_3365754, baseEnd_3365754] using wordTrace_append hprefix tailTrace_3365754
  have hstable : (prefixWord ++ tailWord_3365754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365754).length < 2 ^ (prefixWord ++ tailWord_3365754).sum := by decide
  have hdescent : baseEnd_3365754 < baseStart_3365754 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365764 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3365764 : Nat := 118140960795 + 3365764 * 2 ^ 59
def prefixEnd_3365764 : Nat := 4983230072969 + 3 ^ 40 * 3365764 * 2
def baseEnd_3365764 : Nat := 1728254701599474666571139

theorem tailTrace_3365764 : CollatzResearch.WordTrace tailWord_3365764 prefixEnd_3365764 1728254701599474666571139 := by
  unfold tailWord_3365764
  simp only [CollatzResearch.WordTrace]
  refine ⟨61379749089209664786008173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81839665452279553048010897 61379749089209664786008173)
  ·
    refine ⟨23017405908453624294753065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61379749089209664786008173 23017405908453624294753065)
    ·
      refine ⟨17263054431340218221064799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23017405908453624294753065 17263054431340218221064799)
      ·
        refine ⟨25894581647010327331597199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17263054431340218221064799 25894581647010327331597199)
        ·
          refine ⟨38841872470515490997395799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25894581647010327331597199 38841872470515490997395799)
          ·
            refine ⟨58262808705773236496093699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38841872470515490997395799 58262808705773236496093699)
            ·
              refine ⟨87394213058659854744140549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58262808705773236496093699 87394213058659854744140549)
              ·
                refine ⟨16386414948498722764526353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87394213058659854744140549 16386414948498722764526353)
                ·
                  refine ⟨12289811211374042073394765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16386414948498722764526353 12289811211374042073394765)
                  ·
                    refine ⟨4608679204265265777523037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12289811211374042073394765 4608679204265265777523037)
                    ·
                      refine ⟨1728254701599474666571139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4608679204265265777523037 1728254701599474666571139)
                      ·
                        rfl

theorem cell23_3365764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3365764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365764 prefixEnd_3365764 := by exact prefixLift 3365764
  have htrace : WordTrace (prefixWord ++ tailWord_3365764) baseStart_3365764 baseEnd_3365764 := by
    simpa [prefixWord, tailWord_3365764, baseEnd_3365764] using wordTrace_append hprefix tailTrace_3365764
  have hstable : (prefixWord ++ tailWord_3365764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365764).length < 2 ^ (prefixWord ++ tailWord_3365764).sum := by decide
  have hdescent : baseEnd_3365764 < baseStart_3365764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365771 : List Nat := [1, 1, 1, 1, 4, 2, 6, 2, 5]
def baseStart_3365771 : Nat := 118140960795 + 3365771 * 2 ^ 59
def prefixEnd_3365771 : Nat := 4983230072969 + 3 ^ 40 * 3365771 * 2
def baseEnd_3365771 : Nat := 192028699551561793242623

theorem tailTrace_3365771 : CollatzResearch.WordTrace tailWord_3365771 prefixEnd_3365771 192028699551561793242623 := by
  unfold tailWord_3365771
  simp only [CollatzResearch.WordTrace]
  refine ⟨122759753489393969767521167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81839835659595979845014111 122759753489393969767521167)
  ·
    refine ⟨184139630234090954651281751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122759753489393969767521167 184139630234090954651281751)
    ·
      refine ⟨276209445351136431976922627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184139630234090954651281751 276209445351136431976922627)
      ·
        refine ⟨414314168026704647965383941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276209445351136431976922627 414314168026704647965383941)
        ·
          refine ⟨77683906505007121493509489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 414314168026704647965383941 77683906505007121493509489)
          ·
            refine ⟨58262929878755341120132117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77683906505007121493509489 58262929878755341120132117)
            ·
              refine ⟨2731074838066656615006193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58262929878755341120132117 2731074838066656615006193)
              ·
                refine ⟨2048306128549992461254645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731074838066656615006193 2048306128549992461254645)
                ·
                  refine ⟨192028699551561793242623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2048306128549992461254645 192028699551561793242623)
                  ·
                    rfl

theorem cell23_3365771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 6, 2, 5].length) (baseStart_3365771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365771 prefixEnd_3365771 := by exact prefixLift 3365771
  have htrace : WordTrace (prefixWord ++ tailWord_3365771) baseStart_3365771 baseEnd_3365771 := by
    simpa [prefixWord, tailWord_3365771, baseEnd_3365771] using wordTrace_append hprefix tailTrace_3365771
  have hstable : (prefixWord ++ tailWord_3365771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365771).length < 2 ^ (prefixWord ++ tailWord_3365771).sum := by decide
  have hdescent : baseEnd_3365771 < baseStart_3365771 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365782 : List Nat := [5, 3, 1, 1, 1, 2, 2, 1, 1, 4, 2]
def baseStart_3365782 : Nat := 118140960795 + 3365782 * 2 ^ 59
def prefixEnd_3365782 : Nat := 4983230072969 + 3 ^ 40 * 3365782 * 2
def baseEnd_3365782 : Nat := 1728263944251255596146057

theorem tailTrace_3365782 : CollatzResearch.WordTrace tailWord_3365782 prefixEnd_3365782 1728263944251255596146057 := by
  unfold tailWord_3365782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672509668272132415385725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81840103128236079097447733 7672509668272132415385725)
  ·
    refine ⟨2877191125602049655769647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7672509668272132415385725 2877191125602049655769647)
    ·
      refine ⟨4315786688403074483654471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2877191125602049655769647 4315786688403074483654471)
      ·
        refine ⟨6473680032604611725481707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315786688403074483654471 6473680032604611725481707)
        ·
          refine ⟨9710520048906917588222561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473680032604611725481707 9710520048906917588222561)
          ·
            refine ⟨7282890036680188191166921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710520048906917588222561 7282890036680188191166921)
            ·
              refine ⟨5462167527510141143375191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282890036680188191166921 5462167527510141143375191)
              ·
                refine ⟨8193251291265211715062787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462167527510141143375191 8193251291265211715062787)
                ·
                  refine ⟨12289876936897817572594181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8193251291265211715062787 12289876936897817572594181)
                  ·
                    refine ⟨2304351925668340794861409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12289876936897817572594181 2304351925668340794861409)
                    ·
                      refine ⟨1728263944251255596146057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304351925668340794861409 1728263944251255596146057)
                      ·
                        rfl

theorem cell23_3365782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_3365782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365782 prefixEnd_3365782 := by exact prefixLift 3365782
  have htrace : WordTrace (prefixWord ++ tailWord_3365782) baseStart_3365782 baseEnd_3365782 := by
    simpa [prefixWord, tailWord_3365782, baseEnd_3365782] using wordTrace_append hprefix tailTrace_3365782
  have hstable : (prefixWord ++ tailWord_3365782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365782).length < 2 ^ (prefixWord ++ tailWord_3365782).sum := by decide
  have hdescent : baseEnd_3365782 < baseStart_3365782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365805 : List Nat := [1, 5, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3365805 : Nat := 118140960795 + 3365805 * 2 ^ 59
def prefixEnd_3365805 : Nat := 4983230072969 + 3 ^ 40 * 3365805 * 2
def baseEnd_3365805 : Nat := 192030639367367667350939

theorem tailTrace_3365805 : CollatzResearch.WordTrace tailWord_3365805 prefixEnd_3365805 192030639367367667350939 := by
  unfold tailWord_3365805
  simp only [CollatzResearch.WordTrace]
  refine ⟨122760993571270793574258869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81840662380847195716172579 122760993571270793574258869)
  ·
    refine ⟨11508843147306636897586769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122760993571270793574258869 11508843147306636897586769)
    ·
      refine ⟨8631632360479977673190077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11508843147306636897586769 8631632360479977673190077)
      ·
        refine ⟨3236862135179991627446279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8631632360479977673190077 3236862135179991627446279)
        ·
          refine ⟨4855293202769987441169419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3236862135179991627446279 4855293202769987441169419)
          ·
            refine ⟨7282939804154981161754129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855293202769987441169419 7282939804154981161754129)
            ·
              refine ⟨5462204853116235871315597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7282939804154981161754129 5462204853116235871315597)
              ·
                refine ⟨2048326819918588451743349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5462204853116235871315597 2048326819918588451743349)
                ·
                  refine ⟨192030639367367667350939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2048326819918588451743349 192030639367367667350939)
                  ·
                    rfl

theorem cell23_3365805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3365805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365805 prefixEnd_3365805 := by exact prefixLift 3365805
  have htrace : WordTrace (prefixWord ++ tailWord_3365805) baseStart_3365805 baseEnd_3365805 := by
    simpa [prefixWord, tailWord_3365805, baseEnd_3365805] using wordTrace_append hprefix tailTrace_3365805
  have hstable : (prefixWord ++ tailWord_3365805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365805).length < 2 ^ (prefixWord ++ tailWord_3365805).sum := by decide
  have hdescent : baseEnd_3365805 < baseStart_3365805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365807 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5]
def baseStart_3365807 : Nat := 118140960795 + 3365807 * 2 ^ 59
def prefixEnd_3365807 : Nat := 4983230072969 + 3 ^ 40 * 3365807 * 2
def baseEnd_3365807 : Nat := 1728276781267617998333441

theorem tailTrace_3365807 : CollatzResearch.WordTrace tailWord_3365807 prefixEnd_3365807 1728276781267617998333441 := by
  unfold tailWord_3365807
  simp only [CollatzResearch.WordTrace]
  refine ⟨122761066517263547915831675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81840711011509031943887783 122761066517263547915831675)
  ·
    refine ⟨184141599775895321873747513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122761066517263547915831675 184141599775895321873747513)
    ·
      refine ⟨138106199831921491405310635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184141599775895321873747513 138106199831921491405310635)
      ·
        refine ⟨207159299747882237107965953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138106199831921491405310635 207159299747882237107965953)
        ·
          refine ⟨155369474810911677830974465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207159299747882237107965953 155369474810911677830974465)
          ·
            refine ⟨116527106108183758373230849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155369474810911677830974465 116527106108183758373230849)
            ·
              refine ⟨87395329581137818779923137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116527106108183758373230849 87395329581137818779923137)
              ·
                refine ⟨65546497185853364084942353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87395329581137818779923137 65546497185853364084942353)
                ·
                  refine ⟨49159872889390023063706765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65546497185853364084942353 49159872889390023063706765)
                  ·
                    refine ⟨18434952333521258648890037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49159872889390023063706765 18434952333521258648890037)
                    ·
                      refine ⟨1728276781267617998333441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18434952333521258648890037 1728276781267617998333441)
                      ·
                        rfl

theorem cell23_3365807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 5].length) (baseStart_3365807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365807 prefixEnd_3365807 := by exact prefixLift 3365807
  have htrace : WordTrace (prefixWord ++ tailWord_3365807) baseStart_3365807 baseEnd_3365807 := by
    simpa [prefixWord, tailWord_3365807, baseEnd_3365807] using wordTrace_append hprefix tailTrace_3365807
  have hstable : (prefixWord ++ tailWord_3365807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365807).length < 2 ^ (prefixWord ++ tailWord_3365807).sum := by decide
  have hdescent : baseEnd_3365807 < baseStart_3365807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365827 : List Nat := [1, 1, 1, 3, 1, 1, 2, 5, 8]
def baseStart_3365827 : Nat := 118140960795 + 3365827 * 2 ^ 59
def prefixEnd_3365827 : Nat := 4983230072969 + 3 ^ 40 * 3365827 * 2
def baseEnd_3365827 : Nat := 192031894542300880009261

theorem tailTrace_3365827 : CollatzResearch.WordTrace tailWord_3365827 prefixEnd_3365827 192031894542300880009261 := by
  unfold tailWord_3365827
  simp only [CollatzResearch.WordTrace]
  refine ⟨122761795977191091331559735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81841197318127394221039823 122761795977191091331559735)
  ·
    refine ⟨184142693965786636997339603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122761795977191091331559735 184142693965786636997339603)
    ·
      refine ⟨276214040948679955496009405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184142693965786636997339603 276214040948679955496009405)
      ·
        refine ⟨103580265355754983311003527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276214040948679955496009405 103580265355754983311003527)
        ·
          refine ⟨155370398033632474966505291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103580265355754983311003527 155370398033632474966505291)
          ·
            refine ⟨233055597050448712449757937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155370398033632474966505291 233055597050448712449757937)
            ·
              refine ⟨174791697787836534337318453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233055597050448712449757937 174791697787836534337318453)
              ·
                refine ⟨16386721667609675094123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174791697787836534337318453 16386721667609675094123605)
                ·
                  refine ⟨192031894542300880009261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16386721667609675094123605 192031894542300880009261)
                  ·
                    rfl

theorem cell23_3365827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 5, 8].length) (baseStart_3365827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365827 prefixEnd_3365827 := by exact prefixLift 3365827
  have htrace : WordTrace (prefixWord ++ tailWord_3365827) baseStart_3365827 baseEnd_3365827 := by
    simpa [prefixWord, tailWord_3365827, baseEnd_3365827] using wordTrace_append hprefix tailTrace_3365827
  have hstable : (prefixWord ++ tailWord_3365827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365827).length < 2 ^ (prefixWord ++ tailWord_3365827).sum := by decide
  have hdescent : baseEnd_3365827 < baseStart_3365827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365858 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3365858 : Nat := 118140960795 + 3365858 * 2 ^ 59
def prefixEnd_3365858 : Nat := 4983230072969 + 3 ^ 40 * 3365858 * 2
def baseEnd_3365858 : Nat := 1728302968780997298795707

theorem tailTrace_3365858 : CollatzResearch.WordTrace tailWord_3365858 prefixEnd_3365858 1728302968780997298795707 := by
  unfold tailWord_3365858
  simp only [CollatzResearch.WordTrace]
  refine ⟨30690731660019695906484557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81841951093385855750625485 30690731660019695906484557)
  ·
    refine ⟨11509024372507385964931709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30690731660019695906484557 11509024372507385964931709)
    ·
      refine ⟨4315884139690269736849391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11509024372507385964931709 4315884139690269736849391)
      ·
        refine ⟨6473826209535404605274087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315884139690269736849391 6473826209535404605274087)
        ·
          refine ⟨9710739314303106907911131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473826209535404605274087 9710739314303106907911131)
          ·
            refine ⟨14566108971454660361866697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710739314303106907911131 14566108971454660361866697)
            ·
              refine ⟨10924581728590995271400023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14566108971454660361866697 10924581728590995271400023)
              ·
                refine ⟨16386872592886492907100035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10924581728590995271400023 16386872592886492907100035)
                ·
                  refine ⟨24580308889329739360650053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16386872592886492907100035 24580308889329739360650053)
                  ·
                    refine ⟨4608807916749326130121885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24580308889329739360650053 4608807916749326130121885)
                    ·
                      refine ⟨1728302968780997298795707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4608807916749326130121885 1728302968780997298795707)
                      ·
                        rfl

theorem cell23_3365858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3365858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365858 prefixEnd_3365858 := by exact prefixLift 3365858
  have htrace : WordTrace (prefixWord ++ tailWord_3365858) baseStart_3365858 baseEnd_3365858 := by
    simpa [prefixWord, tailWord_3365858, baseEnd_3365858] using wordTrace_append hprefix tailTrace_3365858
  have hstable : (prefixWord ++ tailWord_3365858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365858).length < 2 ^ (prefixWord ++ tailWord_3365858).sum := by decide
  have hdescent : baseEnd_3365858 < baseStart_3365858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365921 : List Nat := [1, 2, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3365921 : Nat := 118140960795 + 3365921 * 2 ^ 59
def prefixEnd_3365921 : Nat := 4983230072969 + 3 ^ 40 * 3365921 * 2
def baseEnd_3365921 : Nat := 576111772687410184102639

theorem tailTrace_3365921 : CollatzResearch.WordTrace tailWord_3365921 prefixEnd_3365921 576111772687410184102639 := by
  unfold tailWord_3365921
  simp only [CollatzResearch.WordTrace]
  refine ⟨122765224438850545385481617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81843482959233696923654411 122765224438850545385481617)
  ·
    refine ⟨92073918329137909039111213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122765224438850545385481617 92073918329137909039111213)
    ·
      refine ⟨34527719373426715889666705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92073918329137909039111213 34527719373426715889666705)
      ·
        refine ⟨25895789530070036917250029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34527719373426715889666705 25895789530070036917250029)
        ·
          refine ⟨9710921073776263843968761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25895789530070036917250029 9710921073776263843968761)
          ·
            refine ⟨7283190805332197882976571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9710921073776263843968761 7283190805332197882976571)
            ·
              refine ⟨10924786207998296824464857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7283190805332197882976571 10924786207998296824464857)
              ·
                refine ⟨8193589655998722618348643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10924786207998296824464857 8193589655998722618348643)
                ·
                  refine ⟨12290384483998083927522965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8193589655998722618348643 12290384483998083927522965)
                  ·
                    refine ⟨576111772687410184102639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12290384483998083927522965 576111772687410184102639)
                    ·
                      rfl

theorem cell23_3365921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3365921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365921 prefixEnd_3365921 := by exact prefixLift 3365921
  have htrace : WordTrace (prefixWord ++ tailWord_3365921) baseStart_3365921 baseEnd_3365921 := by
    simpa [prefixWord, tailWord_3365921, baseEnd_3365921] using wordTrace_append hprefix tailTrace_3365921
  have hstable : (prefixWord ++ tailWord_3365921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365921).length < 2 ^ (prefixWord ++ tailWord_3365921).sum := by decide
  have hdescent : baseEnd_3365921 < baseStart_3365921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365938 : List Nat := [3, 2, 1, 1, 2, 2, 4, 2, 2, 4]
def baseStart_3365938 : Nat := 118140960795 + 3365938 * 2 ^ 59
def prefixEnd_3365938 : Nat := 4983230072969 + 3 ^ 40 * 3365938 * 2
def baseEnd_3365938 : Nat := 576114682411118995265113

theorem tailTrace_3365938 : CollatzResearch.WordTrace tailWord_3365938 prefixEnd_3365938 576114682411118995265113 := by
  unfold tailWord_3365938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30691461119947239322212617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81843896319859304859233645 30691461119947239322212617)
  ·
    refine ⟨23018595839960429491659463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30691461119947239322212617 23018595839960429491659463)
    ·
      refine ⟨34527893759940644237489195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23018595839960429491659463 34527893759940644237489195)
      ·
        refine ⟨51791840639910966356233793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34527893759940644237489195 51791840639910966356233793)
        ·
          refine ⟨38843880479933224767175345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51791840639910966356233793 38843880479933224767175345)
          ·
            refine ⟨29132910359949918575381509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38843880479933224767175345 29132910359949918575381509)
            ·
              refine ⟨5462420692490609732884033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29132910359949918575381509 5462420692490609732884033)
              ·
                refine ⟨4096815519367957299663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462420692490609732884033 4096815519367957299663025)
                ·
                  refine ⟨3072611639525967974747269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4096815519367957299663025 3072611639525967974747269)
                  ·
                    refine ⟨576114682411118995265113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072611639525967974747269 576114682411118995265113)
                    ·
                      rfl

theorem cell23_3365938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 2, 2, 4].length) (baseStart_3365938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365938 prefixEnd_3365938 := by exact prefixLift 3365938
  have htrace : WordTrace (prefixWord ++ tailWord_3365938) baseStart_3365938 baseEnd_3365938 := by
    simpa [prefixWord, tailWord_3365938, baseEnd_3365938] using wordTrace_append hprefix tailTrace_3365938
  have hstable : (prefixWord ++ tailWord_3365938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365938).length < 2 ^ (prefixWord ++ tailWord_3365938).sum := by decide
  have hdescent : baseEnd_3365938 < baseStart_3365938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3365964 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_3365964 : Nat := 118140960795 + 3365964 * 2 ^ 59
def prefixEnd_3365964 : Nat := 4983230072969 + 3 ^ 40 * 3365964 * 2
def baseEnd_3365964 : Nat := 576119132576791294690073

theorem tailTrace_3365964 : CollatzResearch.WordTrace tailWord_3365964 prefixEnd_3365964 576119132576791294690073 := by
  unfold tailWord_3365964
  simp only [CollatzResearch.WordTrace]
  refine ⟨61383396388847381864648473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81844528518463175819531297 61383396388847381864648473)
  ·
    refine ⟨46037547291635536398486355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61383396388847381864648473 46037547291635536398486355)
    ·
      refine ⟨69056320937453304597729533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46037547291635536398486355 69056320937453304597729533)
      ·
        refine ⟨25896120351544989224148575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69056320937453304597729533 25896120351544989224148575)
        ·
          refine ⟨38844180527317483836222863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25896120351544989224148575 38844180527317483836222863)
          ·
            refine ⟨58266270790976225754334295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38844180527317483836222863 58266270790976225754334295)
            ·
              refine ⟨87399406186464338631501443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58266270790976225754334295 87399406186464338631501443)
              ·
                refine ⟨131099109279696507947252165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87399406186464338631501443 131099109279696507947252165)
                ·
                  refine ⟨24581082989943095240109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131099109279696507947252165 24581082989943095240109781)
                  ·
                    refine ⟨576119132576791294690073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24581082989943095240109781 576119132576791294690073)
                    ·
                      rfl

theorem cell23_3365964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_3365964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3365964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3365964 prefixEnd_3365964 := by exact prefixLift 3365964
  have htrace : WordTrace (prefixWord ++ tailWord_3365964) baseStart_3365964 baseEnd_3365964 := by
    simpa [prefixWord, tailWord_3365964, baseEnd_3365964] using wordTrace_append hprefix tailTrace_3365964
  have hstable : (prefixWord ++ tailWord_3365964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3365964).length < 2 ^ (prefixWord ++ tailWord_3365964).sum := by decide
  have hdescent : baseEnd_3365964 < baseStart_3365964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3365964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366051 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3]
def baseStart_3366051 : Nat := 118140960795 + 3366051 * 2 ^ 59
def prefixEnd_3366051 : Nat := 4983230072969 + 3 ^ 40 * 3366051 * 2
def baseEnd_3366051 : Nat := 1728402070547315043682319

theorem tailTrace_3366051 : CollatzResearch.WordTrace tailWord_3366051 prefixEnd_3366051 1728402070547315043682319 := by
  unfold tailWord_3366051
  simp only [CollatzResearch.WordTrace]
  refine ⟨122769965928379577587714007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81846643952253051725142671 122769965928379577587714007)
  ·
    refine ⟨184154948892569366381571011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122769965928379577587714007 184154948892569366381571011)
    ·
      refine ⟨276232423338854049572356517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184154948892569366381571011 276232423338854049572356517)
      ·
        refine ⟨51793579376035134294816847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276232423338854049572356517 51793579376035134294816847)
        ·
          refine ⟨77690369064052701442225271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51793579376035134294816847 77690369064052701442225271)
          ·
            refine ⟨116535553596079052163337907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77690369064052701442225271 116535553596079052163337907)
            ·
              refine ⟨174803330394118578245006861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116535553596079052163337907 174803330394118578245006861)
              ·
                refine ⟨65551248897794466841877573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174803330394118578245006861 65551248897794466841877573)
                ·
                  refine ⟨12290859168336462532852045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65551248897794466841877573 12290859168336462532852045)
                  ·
                    refine ⟨4609072188126173449819517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12290859168336462532852045 4609072188126173449819517)
                    ·
                      refine ⟨1728402070547315043682319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609072188126173449819517 1728402070547315043682319)
                      ·
                        rfl

theorem cell23_3366051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_3366051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366051 prefixEnd_3366051 := by exact prefixLift 3366051
  have htrace : WordTrace (prefixWord ++ tailWord_3366051) baseStart_3366051 baseEnd_3366051 := by
    simpa [prefixWord, tailWord_3366051, baseEnd_3366051] using wordTrace_append hprefix tailTrace_3366051
  have hstable : (prefixWord ++ tailWord_3366051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366051).length < 2 ^ (prefixWord ++ tailWord_3366051).sum := by decide
  have hdescent : baseEnd_3366051 < baseStart_3366051 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366071 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 4, 5]
def baseStart_3366071 : Nat := 118140960795 + 3366071 * 2 ^ 59
def prefixEnd_3366071 : Nat := 4983230072969 + 3 ^ 40 * 3366071 * 2
def baseEnd_3366071 : Nat := 576137446720134988477409

theorem tailTrace_3366071 : CollatzResearch.WordTrace tailWord_3366071 prefixEnd_3366071 576137446720134988477409 := by
  unfold tailWord_3366071
  simp only [CollatzResearch.WordTrace]
  refine ⟨122770695388307121003442067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81847130258871414002294711 122770695388307121003442067)
  ·
    refine ⟨184156043082460681505163101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122770695388307121003442067 184156043082460681505163101)
    ·
      refine ⟨69058516155922755564436163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184156043082460681505163101 69058516155922755564436163)
      ·
        refine ⟨103587774233884133346654245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69058516155922755564436163 103587774233884133346654245)
        ·
          refine ⟨19422707668853275002497671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103587774233884133346654245 19422707668853275002497671)
          ·
            refine ⟨29134061503279912503746507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19422707668853275002497671 29134061503279912503746507)
            ·
              refine ⟨43701092254919868755619761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29134061503279912503746507 43701092254919868755619761)
              ·
                refine ⟨32775819191189901566714821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43701092254919868755619761 32775819191189901566714821)
                ·
                  refine ⟨6145466098348106543759029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32775819191189901566714821 6145466098348106543759029)
                  ·
                    refine ⟨576137446720134988477409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6145466098348106543759029 576137446720134988477409)
                    ·
                      rfl

theorem cell23_3366071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_3366071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366071 prefixEnd_3366071 := by exact prefixLift 3366071
  have htrace : WordTrace (prefixWord ++ tailWord_3366071) baseStart_3366071 baseEnd_3366071 := by
    simpa [prefixWord, tailWord_3366071, baseEnd_3366071] using wordTrace_append hprefix tailTrace_3366071
  have hstable : (prefixWord ++ tailWord_3366071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366071).length < 2 ^ (prefixWord ++ tailWord_3366071).sum := by decide
  have hdescent : baseEnd_3366071 < baseStart_3366071 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366086 : List Nat := [6, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3366086 : Nat := 118140960795 + 3366086 * 2 ^ 59
def prefixEnd_3366086 : Nat := 4983230072969 + 3 ^ 40 * 3366086 * 2
def baseEnd_3366086 : Nat := 1728420042370222406744659

theorem tailTrace_3366086 : CollatzResearch.WordTrace tailWord_3366086 prefixEnd_3366086 1728420042370222406744659 := by
  unfold tailWord_3366086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836601327601649330163691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81847494988835185710158741 3836601327601649330163691)
  ·
    refine ⟨5754901991402473995245537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3836601327601649330163691 5754901991402473995245537)
    ·
      refine ⟨4316176493551855496434153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5754901991402473995245537 4316176493551855496434153)
      ·
        refine ⟨3237132370163891622325615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4316176493551855496434153 3237132370163891622325615)
        ·
          refine ⟨4855698555245837433488423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237132370163891622325615 4855698555245837433488423)
          ·
            refine ⟨7283547832868756150232635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4855698555245837433488423 7283547832868756150232635)
            ·
              refine ⟨10925321749303134225348953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7283547832868756150232635 10925321749303134225348953)
              ·
                refine ⟨8193991311977350669011715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10925321749303134225348953 8193991311977350669011715)
                ·
                  refine ⟨12290986967966026003517573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8193991311977350669011715 12290986967966026003517573)
                  ·
                    refine ⟨2304560056493629875659545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12290986967966026003517573 2304560056493629875659545)
                    ·
                      refine ⟨1728420042370222406744659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304560056493629875659545 1728420042370222406744659)
                      ·
                        rfl

theorem cell23_3366086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3366086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366086 prefixEnd_3366086 := by exact prefixLift 3366086
  have htrace : WordTrace (prefixWord ++ tailWord_3366086) baseStart_3366086 baseEnd_3366086 := by
    simpa [prefixWord, tailWord_3366086, baseEnd_3366086] using wordTrace_append hprefix tailTrace_3366086
  have hstable : (prefixWord ++ tailWord_3366086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366086).length < 2 ^ (prefixWord ++ tailWord_3366086).sum := by decide
  have hdescent : baseEnd_3366086 < baseStart_3366086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366109 : List Nat := [1, 4, 3, 2, 2, 2, 2, 2, 5]
def baseStart_3366109 : Nat := 118140960795 + 3366109 * 2 ^ 59
def prefixEnd_3366109 : Nat := 4983230072969 + 3 ^ 40 * 3366109 * 2
def baseEnd_3366109 : Nat := 192047983602808424084117

theorem tailTrace_3366109 : CollatzResearch.WordTrace tailWord_3366109 prefixEnd_3366109 192047983602808424084117 := by
  unfold tailWord_3366109
  simp only [CollatzResearch.WordTrace]
  refine ⟨122772081362169453493325381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81848054241446302328883587 122772081362169453493325381)
  ·
    refine ⟨23019765255406772529998509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122772081362169453493325381 23019765255406772529998509)
    ·
      refine ⟨8632411970777539698749441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23019765255406772529998509 8632411970777539698749441)
      ·
        refine ⟨6474308978083154774062081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8632411970777539698749441 6474308978083154774062081)
        ·
          refine ⟨4855731733562366080546561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6474308978083154774062081 4855731733562366080546561)
          ·
            refine ⟨3641798800171774560409921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4855731733562366080546561 3641798800171774560409921)
            ·
              refine ⟨2731349100128830920307441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3641798800171774560409921 2731349100128830920307441)
              ·
                refine ⟨2048511825096623190230581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731349100128830920307441 2048511825096623190230581)
                ·
                  refine ⟨192047983602808424084117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2048511825096623190230581 192047983602808424084117)
                  ·
                    rfl

theorem cell23_3366109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_3366109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366109 prefixEnd_3366109 := by exact prefixLift 3366109
  have htrace : WordTrace (prefixWord ++ tailWord_3366109) baseStart_3366109 baseEnd_3366109 := by
    simpa [prefixWord, tailWord_3366109, baseEnd_3366109] using wordTrace_append hprefix tailTrace_3366109
  have hstable : (prefixWord ++ tailWord_3366109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366109).length < 2 ^ (prefixWord ++ tailWord_3366109).sum := by decide
  have hdescent : baseEnd_3366109 < baseStart_3366109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366125 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 1, 6, 2]
def baseStart_3366125 : Nat := 118140960795 + 3366125 * 2 ^ 59
def prefixEnd_3366125 : Nat := 4983230072969 + 3 ^ 40 * 3366125 * 2
def baseEnd_3366125 : Nat := 1728440068115747754156979

theorem tailTrace_3366125 : CollatzResearch.WordTrace tailWord_3366125 prefixEnd_3366125 1728440068115747754156979 := by
  unfold tailWord_3366125
  simp only [CollatzResearch.WordTrace]
  refine ⟨122772664930111488225907829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81848443286740992150605219 122772664930111488225907829)
  ·
    refine ⟨11509937337197952021178859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122772664930111488225907829 11509937337197952021178859)
    ·
      refine ⟨17264906005796928031768289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11509937337197952021178859 17264906005796928031768289)
      ·
        refine ⟨12948679504347696023826217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17264906005796928031768289 12948679504347696023826217)
        ·
          refine ⟨9711509628260772017869663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12948679504347696023826217 9711509628260772017869663)
          ·
            refine ⟨14567264442391158026804495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9711509628260772017869663 14567264442391158026804495)
            ·
              refine ⟨21850896663586737040206743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14567264442391158026804495 21850896663586737040206743)
              ·
                refine ⟨32776344995380105560310115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21850896663586737040206743 32776344995380105560310115)
                ·
                  refine ⟨49164517493070158340465173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32776344995380105560310115 49164517493070158340465173)
                  ·
                    refine ⟨2304586757487663672209305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49164517493070158340465173 2304586757487663672209305)
                    ·
                      refine ⟨1728440068115747754156979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304586757487663672209305 1728440068115747754156979)
                      ·
                        rfl

theorem cell23_3366125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_3366125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366125 prefixEnd_3366125 := by exact prefixLift 3366125
  have htrace : WordTrace (prefixWord ++ tailWord_3366125) baseStart_3366125 baseEnd_3366125 := by
    simpa [prefixWord, tailWord_3366125, baseEnd_3366125] using wordTrace_append hprefix tailTrace_3366125
  have hstable : (prefixWord ++ tailWord_3366125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366125).length < 2 ^ (prefixWord ++ tailWord_3366125).sum := by decide
  have hdescent : baseEnd_3366125 < baseStart_3366125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366142 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4]
def baseStart_3366142 : Nat := 118140960795 + 3366142 * 2 ^ 59
def prefixEnd_3366142 : Nat := 4983230072969 + 3 ^ 40 * 3366142 * 2
def baseEnd_3366142 : Nat := 1728448797286874187644401

theorem tailTrace_3366142 : CollatzResearch.WordTrace tailWord_3366142 prefixEnd_3366142 1728448797286874187644401 := by
  unfold tailWord_3366142
  simp only [CollatzResearch.WordTrace]
  refine ⟨15346660621381237516159585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81848856647366600086184453 15346660621381237516159585)
  ·
    refine ⟨11509995466035928137119689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15346660621381237516159585 11509995466035928137119689)
    ·
      refine ⟨8632496599526946102839767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11509995466035928137119689 8632496599526946102839767)
      ·
        refine ⟨12948744899290419154259651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8632496599526946102839767 12948744899290419154259651)
        ·
          refine ⟨19423117348935628731389477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12948744899290419154259651 19423117348935628731389477)
          ·
            refine ⟨3641834502925430387135527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19423117348935628731389477 3641834502925430387135527)
            ·
              refine ⟨5462751754388145580703291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3641834502925430387135527 5462751754388145580703291)
              ·
                refine ⟨8194127631582218371054937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462751754388145580703291 8194127631582218371054937)
                ·
                  refine ⟨6145595723686663778291203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8194127631582218371054937 6145595723686663778291203)
                  ·
                    refine ⟨9218393585529995667436805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145595723686663778291203 9218393585529995667436805)
                    ·
                      refine ⟨1728448797286874187644401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9218393585529995667436805 1728448797286874187644401)
                      ·
                        rfl

theorem cell23_3366142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_3366142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366142 prefixEnd_3366142 := by exact prefixLift 3366142
  have htrace : WordTrace (prefixWord ++ tailWord_3366142) baseStart_3366142 baseEnd_3366142 := by
    simpa [prefixWord, tailWord_3366142, baseEnd_3366142] using wordTrace_append hprefix tailTrace_3366142
  have hstable : (prefixWord ++ tailWord_3366142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366142).length < 2 ^ (prefixWord ++ tailWord_3366142).sum := by decide
  have hdescent : baseEnd_3366142 < baseStart_3366142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366145 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 3]
def baseStart_3366145 : Nat := 118140960795 + 3366145 * 2 ^ 59
def prefixEnd_3366145 : Nat := 4983230072969 + 3 ^ 40 * 3366145 * 2
def baseEnd_3366145 : Nat := 1728450337728837675906887

theorem tailTrace_3366145 : CollatzResearch.WordTrace tailWord_3366145 prefixEnd_3366145 1728450337728837675906887 := by
  unfold tailWord_3366145
  simp only [CollatzResearch.WordTrace]
  refine ⟨122773394390039031641635889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81848929593359354427757259 122773394390039031641635889)
  ·
    refine ⟨92080045792529273731226917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122773394390039031641635889 92080045792529273731226917)
    ·
      refine ⟨17265008586099238824605047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92080045792529273731226917 17265008586099238824605047)
      ·
        refine ⟨25897512879148858236907571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17265008586099238824605047 25897512879148858236907571)
        ·
          refine ⟨38846269318723287355361357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25897512879148858236907571 38846269318723287355361357)
          ·
            refine ⟨14567350994521232758260509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38846269318723287355361357 14567350994521232758260509)
            ·
              refine ⟨5462756622945462284347691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14567350994521232758260509 5462756622945462284347691)
              ·
                refine ⟨8194134934418193426521537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5462756622945462284347691 8194134934418193426521537)
                ·
                  refine ⟨6145601200813645069891153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8194134934418193426521537 6145601200813645069891153)
                  ·
                    refine ⟨4609200900610233802418365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145601200813645069891153 4609200900610233802418365)
                    ·
                      refine ⟨1728450337728837675906887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609200900610233802418365 1728450337728837675906887)
                      ·
                        rfl

theorem cell23_3366145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_3366145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366145 prefixEnd_3366145 := by exact prefixLift 3366145
  have htrace : WordTrace (prefixWord ++ tailWord_3366145) baseStart_3366145 baseEnd_3366145 := by
    simpa [prefixWord, tailWord_3366145, baseEnd_3366145] using wordTrace_append hprefix tailTrace_3366145
  have hstable : (prefixWord ++ tailWord_3366145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366145).length < 2 ^ (prefixWord ++ tailWord_3366145).sum := by decide
  have hdescent : baseEnd_3366145 < baseStart_3366145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366195 : List Nat := [1, 1, 1, 2, 5, 3, 2, 2, 1, 5]
def baseStart_3366195 : Nat := 118140960795 + 3366195 * 2 ^ 59
def prefixEnd_3366195 : Nat := 4983230072969 + 3 ^ 40 * 3366195 * 2
def baseEnd_3366195 : Nat := 576158670587187493427219

theorem tailTrace_3366195 : CollatzResearch.WordTrace tailWord_3366195 prefixEnd_3366195 576158670587187493427219 := by
  unfold tailWord_3366195
  simp only [CollatzResearch.WordTrace]
  refine ⟨122775218039857890180956039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81850145359905260120637359 122775218039857890180956039)
  ·
    refine ⟨184162827059786835271434059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122775218039857890180956039 184162827059786835271434059)
    ·
      refine ⟨276244240589680252907151089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184162827059786835271434059 276244240589680252907151089)
      ·
        refine ⟨207183180442260189680363317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276244240589680252907151089 207183180442260189680363317)
        ·
          refine ⟨19423423166461892782534061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207183180442260189680363317 19423423166461892782534061)
          ·
            refine ⟨7283783687423209793450273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19423423166461892782534061 7283783687423209793450273)
            ·
              refine ⟨5462837765567407345087705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7283783687423209793450273 5462837765567407345087705)
              ·
                refine ⟨4097128324175555508815779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462837765567407345087705 4097128324175555508815779)
                ·
                  refine ⟨6145692486263333263223669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097128324175555508815779 6145692486263333263223669)
                  ·
                    refine ⟨576158670587187493427219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6145692486263333263223669 576158670587187493427219)
                    ·
                      rfl

theorem cell23_3366195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 5].length) (baseStart_3366195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366195 prefixEnd_3366195 := by exact prefixLift 3366195
  have htrace : WordTrace (prefixWord ++ tailWord_3366195) baseStart_3366195 baseEnd_3366195 := by
    simpa [prefixWord, tailWord_3366195, baseEnd_3366195] using wordTrace_append hprefix tailTrace_3366195
  have hstable : (prefixWord ++ tailWord_3366195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366195).length < 2 ^ (prefixWord ++ tailWord_3366195).sum := by decide
  have hdescent : baseEnd_3366195 < baseStart_3366195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366208 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_3366208 : Nat := 118140960795 + 3366208 * 2 ^ 59
def prefixEnd_3366208 : Nat := 4983230072969 + 3 ^ 40 * 3366208 * 2
def baseEnd_3366208 : Nat := 576160895670023643139699

theorem tailTrace_3366208 : CollatzResearch.WordTrace tailWord_3366208 prefixEnd_3366208 576160895670023643139699 := by
  unfold tailWord_3366208
  simp only [CollatzResearch.WordTrace]
  refine ⟨61387846094405396700589639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81850461459207195600786185 61387846094405396700589639)
  ·
    refine ⟨92081769141608095050884459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61387846094405396700589639 92081769141608095050884459)
    ·
      refine ⟨138122653712412142576326689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92081769141608095050884459 138122653712412142576326689)
      ·
        refine ⟨103591990284309106932245017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138122653712412142576326689 103591990284309106932245017)
        ·
          refine ⟨77693992713231830199183763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103591990284309106932245017 77693992713231830199183763)
          ·
            refine ⟨116540989069847745298775645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77693992713231830199183763 116540989069847745298775645)
            ·
              refine ⟨43702870901192904487040867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116540989069847745298775645 43702870901192904487040867)
              ·
                refine ⟨65554306351789356730561301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43702870901192904487040867 65554306351789356730561301)
                ·
                  refine ⟨3072858110240126096745061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65554306351789356730561301 3072858110240126096745061)
                  ·
                    refine ⟨576160895670023643139699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072858110240126096745061 576160895670023643139699)
                    ·
                      rfl

theorem cell23_3366208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_3366208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366208 prefixEnd_3366208 := by exact prefixLift 3366208
  have htrace : WordTrace (prefixWord ++ tailWord_3366208) baseStart_3366208 baseEnd_3366208 := by
    simpa [prefixWord, tailWord_3366208, baseEnd_3366208] using wordTrace_append hprefix tailTrace_3366208
  have hstable : (prefixWord ++ tailWord_3366208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366208).length < 2 ^ (prefixWord ++ tailWord_3366208).sum := by decide
  have hdescent : baseEnd_3366208 < baseStart_3366208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366212 : List Nat := [2, 3, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3366212 : Nat := 118140960795 + 3366212 * 2 ^ 59
def prefixEnd_3366212 : Nat := 4983230072969 + 3 ^ 40 * 3366212 * 2
def baseEnd_3366212 : Nat := 576161580310896304589693

theorem tailTrace_3366212 : CollatzResearch.WordTrace tailWord_3366212 prefixEnd_3366212 576161580310896304589693 := by
  unfold tailWord_3366212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61387919040398151042162445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81850558720530868056216593 61387919040398151042162445)
  ·
    refine ⟨23020469640149306640810917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61387919040398151042162445 23020469640149306640810917)
    ·
      refine ⟨4316338057527994995152047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23020469640149306640810917 4316338057527994995152047)
      ·
        refine ⟨6474507086291992492728071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316338057527994995152047 6474507086291992492728071)
        ·
          refine ⟨9711760629437988739092107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6474507086291992492728071 9711760629437988739092107)
          ·
            refine ⟨14567640944156983108638161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9711760629437988739092107 14567640944156983108638161)
            ·
              refine ⟨10925730708117737331478621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14567640944156983108638161 10925730708117737331478621)
              ·
                refine ⟨4097149015544151499304483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10925730708117737331478621 4097149015544151499304483)
                ·
                  refine ⟨6145723523316227248956725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097149015544151499304483 6145723523316227248956725)
                  ·
                    refine ⟨576161580310896304589693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6145723523316227248956725 576161580310896304589693)
                    ·
                      rfl

theorem cell23_3366212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3366212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366212 prefixEnd_3366212 := by exact prefixLift 3366212
  have htrace : WordTrace (prefixWord ++ tailWord_3366212) baseStart_3366212 baseEnd_3366212 := by
    simpa [prefixWord, tailWord_3366212, baseEnd_3366212] using wordTrace_append hprefix tailTrace_3366212
  have hstable : (prefixWord ++ tailWord_3366212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366212).length < 2 ^ (prefixWord ++ tailWord_3366212).sum := by decide
  have hdescent : baseEnd_3366212 < baseStart_3366212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366215 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_3366215 : Nat := 118140960795 + 3366215 * 2 ^ 59
def prefixEnd_3366215 : Nat := 4983230072969 + 3 ^ 40 * 3366215 * 2
def baseEnd_3366215 : Nat := 1728486281374652402031565

theorem tailTrace_3366215 : CollatzResearch.WordTrace tailWord_3366215 prefixEnd_3366215 1728486281374652402031565 := by
  unfold tailWord_3366215
  simp only [CollatzResearch.WordTrace]
  refine ⟨122775947499785433596684099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81850631666523622397789399 122775947499785433596684099)
  ·
    refine ⟨184163921249678150395026149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122775947499785433596684099 184163921249678150395026149)
    ·
      refine ⟨34530735234314653199067403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184163921249678150395026149 34530735234314653199067403)
      ·
        refine ⟨51796102851471979798601105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34530735234314653199067403 51796102851471979798601105)
        ·
          refine ⟨38847077138603984848950829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51796102851471979798601105 38847077138603984848950829)
          ·
            refine ⟨14567653926976494318356561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38847077138603984848950829 14567653926976494318356561)
            ·
              refine ⟨10925740445232370738767421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14567653926976494318356561 10925740445232370738767421)
              ·
                refine ⟨4097152666962139027037783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10925740445232370738767421 4097152666962139027037783)
                ·
                  refine ⟨6145729000443208540556675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097152666962139027037783 6145729000443208540556675)
                  ·
                    refine ⟨9218593500664812810835013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6145729000443208540556675 9218593500664812810835013)
                    ·
                      refine ⟨1728486281374652402031565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9218593500664812810835013 1728486281374652402031565)
                      ·
                        rfl

theorem cell23_3366215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_3366215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366215 prefixEnd_3366215 := by exact prefixLift 3366215
  have htrace : WordTrace (prefixWord ++ tailWord_3366215) baseStart_3366215 baseEnd_3366215 := by
    simpa [prefixWord, tailWord_3366215, baseEnd_3366215] using wordTrace_append hprefix tailTrace_3366215
  have hstable : (prefixWord ++ tailWord_3366215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366215).length < 2 ^ (prefixWord ++ tailWord_3366215).sum := by decide
  have hdescent : baseEnd_3366215 < baseStart_3366215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366225 : List Nat := [1, 2, 2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_3366225 : Nat := 118140960795 + 3366225 * 2 ^ 59
def prefixEnd_3366225 : Nat := 4983230072969 + 3 ^ 40 * 3366225 * 2
def baseEnd_3366225 : Nat := 576163805393732454302173

theorem tailTrace_3366225 : CollatzResearch.WordTrace tailWord_3366225 prefixEnd_3366225 576163805393732454302173 := by
  unfold tailWord_3366225
  simp only [CollatzResearch.WordTrace]
  refine ⟨122776312229749205304548129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81850874819832803536365419 122776312229749205304548129)
  ·
    refine ⟨92082234172311903978411097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122776312229749205304548129 92082234172311903978411097)
    ·
      refine ⟨69061675629233927983808323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92082234172311903978411097 69061675629233927983808323)
      ·
        refine ⟨103592513443850891975712485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69061675629233927983808323 103592513443850891975712485)
        ·
          refine ⟨19423596270722042245446091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103592513443850891975712485 19423596270722042245446091)
          ·
            refine ⟨29135394406083063368169137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19423596270722042245446091 29135394406083063368169137)
            ·
              refine ⟨21851545804562297526126853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29135394406083063368169137 21851545804562297526126853)
              ·
                refine ⟨4097164838355430786148785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21851545804562297526126853 4097164838355430786148785)
                ·
                  refine ⟨3072873628766573089611589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4097164838355430786148785 3072873628766573089611589)
                  ·
                    refine ⟨576163805393732454302173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072873628766573089611589 576163805393732454302173)
                    ·
                      rfl

theorem cell23_3366225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_3366225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366225 prefixEnd_3366225 := by exact prefixLift 3366225
  have htrace : WordTrace (prefixWord ++ tailWord_3366225) baseStart_3366225 baseEnd_3366225 := by
    simpa [prefixWord, tailWord_3366225, baseEnd_3366225] using wordTrace_append hprefix tailTrace_3366225
  have hstable : (prefixWord ++ tailWord_3366225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366225).length < 2 ^ (prefixWord ++ tailWord_3366225).sum := by decide
  have hdescent : baseEnd_3366225 < baseStart_3366225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366228 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_3366228 : Nat := 118140960795 + 3366228 * 2 ^ 59
def prefixEnd_3366228 : Nat := 4983230072969 + 3 ^ 40 * 3366228 * 2
def baseEnd_3366228 : Nat := 1728492956623160851169005

theorem tailTrace_3366228 : CollatzResearch.WordTrace tailWord_3366228 prefixEnd_3366228 1728492956623160851169005 := by
  unfold tailWord_3366228
  simp only [CollatzResearch.WordTrace]
  refine ⟨61388210824369168408453669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81850947765825557877938225 61388210824369168408453669)
  ·
    refine ⟨11510289529569219076585063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61388210824369168408453669 11510289529569219076585063)
    ·
      refine ⟨17265434294353828614877595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11510289529569219076585063 17265434294353828614877595)
      ·
        refine ⟨25898151441530742922316393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17265434294353828614877595 25898151441530742922316393)
        ·
          refine ⟨19423613581148057191737295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25898151441530742922316393 19423613581148057191737295)
          ·
            refine ⟨29135420371722085787605943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19423613581148057191737295 29135420371722085787605943)
            ·
              refine ⟨43703130557583128681408915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29135420371722085787605943 43703130557583128681408915)
              ·
                refine ⟨65554695836374693022113373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43703130557583128681408915 65554695836374693022113373)
                ·
                  refine ⟨24583010938640509883292515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65554695836374693022113373 24583010938640509883292515)
                  ·
                    refine ⟨36874516407960764824938773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24583010938640509883292515 36874516407960764824938773)
                    ·
                      refine ⟨1728492956623160851169005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36874516407960764824938773 1728492956623160851169005)
                      ·
                        rfl

theorem cell23_3366228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_3366228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366228 prefixEnd_3366228 := by exact prefixLift 3366228
  have htrace : WordTrace (prefixWord ++ tailWord_3366228) baseStart_3366228 baseEnd_3366228 := by
    simpa [prefixWord, tailWord_3366228, baseEnd_3366228] using wordTrace_append hprefix tailTrace_3366228
  have hstable : (prefixWord ++ tailWord_3366228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366228).length < 2 ^ (prefixWord ++ tailWord_3366228).sum := by decide
  have hdescent : baseEnd_3366228 < baseStart_3366228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366242 : List Nat := [3, 3, 2, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3366242 : Nat := 118140960795 + 3366242 * 2 ^ 59
def prefixEnd_3366242 : Nat := 4983230072969 + 3 ^ 40 * 3366242 * 2
def baseEnd_3366242 : Nat := 576166715117441265464647

theorem tailTrace_3366242 : CollatzResearch.WordTrace tailWord_3366242 prefixEnd_3366242 576166715117441265464647 := by
  unfold tailWord_3366242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30694233067671904301979245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81851288180458411471944653 30694233067671904301979245)
  ·
    refine ⟨11510337400376964113242217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30694233067671904301979245 11510337400376964113242217)
    ·
      refine ⟨8632753050282723084931663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11510337400376964113242217 8632753050282723084931663)
      ·
        refine ⟨12949129575424084627397495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8632753050282723084931663 12949129575424084627397495)
        ·
          refine ⟨19423694363136126941096243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12949129575424084627397495 19423694363136126941096243)
          ·
            refine ⟨29135541544704190411644365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19423694363136126941096243 29135541544704190411644365)
            ·
              refine ⟨10925828079264071404366637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29135541544704190411644365 10925828079264071404366637)
              ·
                refine ⟨4097185529724026776637489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10925828079264071404366637 4097185529724026776637489)
                ·
                  refine ⟨3072889147293020082478117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4097185529724026776637489 3072889147293020082478117)
                  ·
                    refine ⟨576166715117441265464647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3072889147293020082478117 576166715117441265464647)
                    ·
                      rfl

theorem cell23_3366242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3366242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366242 prefixEnd_3366242 := by exact prefixLift 3366242
  have htrace : WordTrace (prefixWord ++ tailWord_3366242) baseStart_3366242 baseEnd_3366242 := by
    simpa [prefixWord, tailWord_3366242, baseEnd_3366242] using wordTrace_append hprefix tailTrace_3366242
  have hstable : (prefixWord ++ tailWord_3366242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366242).length < 2 ^ (prefixWord ++ tailWord_3366242).sum := by decide
  have hdescent : baseEnd_3366242 < baseStart_3366242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366252 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_3366252 : Nat := 118140960795 + 3366252 * 2 ^ 59
def prefixEnd_3366252 : Nat := 4983230072969 + 3 ^ 40 * 3366252 * 2
def baseEnd_3366252 : Nat := 1728505280158868757268895

theorem tailTrace_3366252 : CollatzResearch.WordTrace tailWord_3366252 prefixEnd_3366252 1728505280158868757268895 := by
  unfold tailWord_3366252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61388648500325694457890505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81851531333767592610520673 61388648500325694457890505)
  ·
    refine ⟨46041486375244270843417879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61388648500325694457890505 46041486375244270843417879)
    ·
      refine ⟨69062229562866406265126819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46041486375244270843417879 69062229562866406265126819)
      ·
        refine ⟨103593344344299609397690229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69062229562866406265126819 103593344344299609397690229)
        ·
          refine ⟨9711876032278088381033459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103593344344299609397690229 9711876032278088381033459)
          ·
            refine ⟨14567814048417132571550189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9711876032278088381033459 14567814048417132571550189)
            ·
              refine ⟨5462930268156424714331321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14567814048417132571550189 5462930268156424714331321)
              ·
                refine ⟨4097197701117318535748491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5462930268156424714331321 4097197701117318535748491)
                ·
                  refine ⟨6145796551675977803622737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097197701117318535748491 6145796551675977803622737)
                  ·
                    refine ⟨4609347413756983352717053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6145796551675977803622737 4609347413756983352717053)
                    ·
                      refine ⟨1728505280158868757268895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609347413756983352717053 1728505280158868757268895)
                      ·
                        rfl

theorem cell23_3366252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_3366252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366252 prefixEnd_3366252 := by exact prefixLift 3366252
  have htrace : WordTrace (prefixWord ++ tailWord_3366252) baseStart_3366252 baseEnd_3366252 := by
    simpa [prefixWord, tailWord_3366252, baseEnd_3366252] using wordTrace_append hprefix tailTrace_3366252
  have hstable : (prefixWord ++ tailWord_3366252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366252).length < 2 ^ (prefixWord ++ tailWord_3366252).sum := by decide
  have hdescent : baseEnd_3366252 < baseStart_3366252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366265 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3366265 : Nat := 118140960795 + 3366265 * 2 ^ 59
def prefixEnd_3366265 : Nat := 4983230072969 + 3 ^ 40 * 3366265 * 2
def baseEnd_3366265 : Nat := 1728511955407377206406335

theorem tailTrace_3366265 : CollatzResearch.WordTrace tailWord_3366265 prefixEnd_3366265 1728511955407377206406335 := by
  unfold tailWord_3366265
  simp only [CollatzResearch.WordTrace]
  refine ⟨122777771149604292136004249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81851847433069528090669499 122777771149604292136004249)
  ·
    refine ⟨92083328362203219102003187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122777771149604292136004249 92083328362203219102003187)
    ·
      refine ⟨138124992543304828653004781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92083328362203219102003187 138124992543304828653004781)
      ·
        refine ⟨51796872203739310744876793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138124992543304828653004781 51796872203739310744876793)
        ·
          refine ⟨38847654152804483058657595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51796872203739310744876793 38847654152804483058657595)
          ·
            refine ⟨58271481229206724587986393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38847654152804483058657595 58271481229206724587986393)
            ·
              refine ⟨43703610921905043440989795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58271481229206724587986393 43703610921905043440989795)
              ·
                refine ⟨65555416382857565161484693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43703610921905043440989795 65555416382857565161484693)
                ·
                  refine ⟨3072910142946448366944595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65555416382857565161484693 3072910142946448366944595)
                  ·
                    refine ⟨4609365214419672550416893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3072910142946448366944595 4609365214419672550416893)
                    ·
                      refine ⟨1728511955407377206406335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609365214419672550416893 1728511955407377206406335)
                      ·
                        rfl

theorem cell23_3366265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3366265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366265 prefixEnd_3366265 := by exact prefixLift 3366265
  have htrace : WordTrace (prefixWord ++ tailWord_3366265) baseStart_3366265 baseEnd_3366265 := by
    simpa [prefixWord, tailWord_3366265, baseEnd_3366265] using wordTrace_append hprefix tailTrace_3366265
  have hstable : (prefixWord ++ tailWord_3366265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366265).length < 2 ^ (prefixWord ++ tailWord_3366265).sum := by decide
  have hdescent : baseEnd_3366265 < baseStart_3366265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366339 : List Nat := [1, 1, 1, 3, 1, 1, 7, 2, 2, 2, 2]
def baseStart_3366339 : Nat := 118140960795 + 3366339 * 2 ^ 59
def prefixEnd_3366339 : Nat := 4983230072969 + 3 ^ 40 * 3366339 * 2
def baseEnd_3366339 : Nat := 1728549952975809916880995

theorem tailTrace_3366339 : CollatzResearch.WordTrace tailWord_3366339 prefixEnd_3366339 1728549952975809916880995 := by
  unfold tailWord_3366339
  simp only [CollatzResearch.WordTrace]
  refine ⟨122780470151336202774198071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81853646767557468516132047 122780470151336202774198071)
  ·
    refine ⟨184170705227004304161297107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122780470151336202774198071 184170705227004304161297107)
    ·
      refine ⟨276256057840506456241945661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184170705227004304161297107 276256057840506456241945661)
      ·
        refine ⟨103596021690189921090729623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276256057840506456241945661 103596021690189921090729623)
        ·
          refine ⟨155394032535284881636094435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103596021690189921090729623 155394032535284881636094435)
          ·
            refine ⟨233091048802927322454141653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155394032535284881636094435 233091048802927322454141653)
            ·
              refine ⟨5463071456318609120018945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 233091048802927322454141653 5463071456318609120018945)
              ·
                refine ⟨4097303592238956840014209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463071456318609120018945 4097303592238956840014209)
                ·
                  refine ⟨3072977694179217630010657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4097303592238956840014209 3072977694179217630010657)
                  ·
                    refine ⟨2304733270634413222507993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3072977694179217630010657 2304733270634413222507993)
                    ·
                      refine ⟨1728549952975809916880995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304733270634413222507993 1728549952975809916880995)
                      ·
                        rfl

theorem cell23_3366339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 2, 2, 2, 2].length) (baseStart_3366339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366339 prefixEnd_3366339 := by exact prefixLift 3366339
  have htrace : WordTrace (prefixWord ++ tailWord_3366339) baseStart_3366339 baseEnd_3366339 := by
    simpa [prefixWord, tailWord_3366339, baseEnd_3366339] using wordTrace_append hprefix tailTrace_3366339
  have hstable : (prefixWord ++ tailWord_3366339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366339).length < 2 ^ (prefixWord ++ tailWord_3366339).sum := by decide
  have hdescent : baseEnd_3366339 < baseStart_3366339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366356 : List Nat := [2, 4, 1, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_3366356 : Nat := 118140960795 + 3366356 * 2 ^ 59
def prefixEnd_3366356 : Nat := 4983230072969 + 3 ^ 40 * 3366356 * 2
def baseEnd_3366356 : Nat := 1728558682146936350368417

theorem tailTrace_3366356 : CollatzResearch.WordTrace tailWord_3366356 prefixEnd_3366356 1728558682146936350368417 := by
  unfold tailWord_3366356
  simp only [CollatzResearch.WordTrace]
  refine ⟨61390545096137307338783461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81854060128183076451711281 61390545096137307338783461)
  ·
    refine ⟨11510727205525745126021899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61390545096137307338783461 11510727205525745126021899)
    ·
      refine ⟨17266090808288617689032849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11510727205525745126021899 17266090808288617689032849)
      ·
        refine ⟨12949568106216463266774637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17266090808288617689032849 12949568106216463266774637)
        ·
          refine ⟨4856088039831173725040489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12949568106216463266774637 4856088039831173725040489)
          ·
            refine ⟨3642066029873380293780367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4856088039831173725040489 3642066029873380293780367)
            ·
              refine ⟨5463099044810070440670551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642066029873380293780367 5463099044810070440670551)
              ·
                refine ⟨8194648567215105661005827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463099044810070440670551 8194648567215105661005827)
                ·
                  refine ⟨12291972850822658491508741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8194648567215105661005827 12291972850822658491508741)
                  ·
                    refine ⟨2304744909529248467157889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12291972850822658491508741 2304744909529248467157889)
                    ·
                      refine ⟨1728558682146936350368417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304744909529248467157889 1728558682146936350368417)
                      ·
                        rfl

theorem cell23_3366356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_3366356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366356 prefixEnd_3366356 := by exact prefixLift 3366356
  have htrace : WordTrace (prefixWord ++ tailWord_3366356) baseStart_3366356 baseEnd_3366356 := by
    simpa [prefixWord, tailWord_3366356, baseEnd_3366356] using wordTrace_append hprefix tailTrace_3366356
  have hstable : (prefixWord ++ tailWord_3366356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366356).length < 2 ^ (prefixWord ++ tailWord_3366356).sum := by decide
  have hdescent : baseEnd_3366356 < baseStart_3366356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366368 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_3366368 : Nat := 118140960795 + 3366368 * 2 ^ 59
def prefixEnd_3366368 : Nat := 4983230072969 + 3 ^ 40 * 3366368 * 2
def baseEnd_3366368 : Nat := 1728564843914790303418361

theorem tailTrace_3366368 : CollatzResearch.WordTrace tailWord_3366368 prefixEnd_3366368 1728564843914790303418361 := by
  unfold tailWord_3366368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61390763934115570363501879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81854351912154093818002505 61390763934115570363501879)
  ·
    refine ⟨92086145901173355545252819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61390763934115570363501879 92086145901173355545252819)
    ·
      refine ⟨138129218851760033317879229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92086145901173355545252819 138129218851760033317879229)
      ·
        refine ⟨51798457069410012494204711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138129218851760033317879229 51798457069410012494204711)
        ·
          refine ⟨77697685604115018741307067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51798457069410012494204711 77697685604115018741307067)
          ·
            refine ⟨116546528406172528111960601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77697685604115018741307067 116546528406172528111960601)
            ·
              refine ⟨87409896304629396083970451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116546528406172528111960601 87409896304629396083970451)
              ·
                refine ⟨131114844456944094125955677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87409896304629396083970451 131114844456944094125955677)
                ·
                  refine ⟨49168066671354035297233379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131114844456944094125955677 49168066671354035297233379)
                  ·
                    refine ⟨73752100007031052945850069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49168066671354035297233379 73752100007031052945850069)
                    ·
                      refine ⟨1728564843914790303418361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73752100007031052945850069 1728564843914790303418361)
                      ·
                        rfl

theorem cell23_3366368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_3366368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366368 prefixEnd_3366368 := by exact prefixLift 3366368
  have htrace : WordTrace (prefixWord ++ tailWord_3366368) baseStart_3366368 baseEnd_3366368 := by
    simpa [prefixWord, tailWord_3366368, baseEnd_3366368] using wordTrace_append hprefix tailTrace_3366368
  have hstable : (prefixWord ++ tailWord_3366368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366368).length < 2 ^ (prefixWord ++ tailWord_3366368).sum := by decide
  have hdescent : baseEnd_3366368 < baseStart_3366368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366375 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3366375 : Nat := 118140960795 + 3366375 * 2 ^ 59
def prefixEnd_3366375 : Nat := 4983230072969 + 3 ^ 40 * 3366375 * 2
def baseEnd_3366375 : Nat := 576189479426457258676943

theorem tailTrace_3366375 : CollatzResearch.WordTrace tailWord_3366375 prefixEnd_3366375 576189479426457258676943 := by
  unfold tailWord_3366375
  simp only [CollatzResearch.WordTrace]
  refine ⟨122781783179205780922508579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81854522119470520615005719 122781783179205780922508579)
  ·
    refine ⟨184172674768808671383762869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122781783179205780922508579 184172674768808671383762869)
    ·
      refine ⟨17266188259575812942227769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184172674768808671383762869 17266188259575812942227769)
      ·
        refine ⟨12949641194681859706670827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17266188259575812942227769 12949641194681859706670827)
        ·
          refine ⟨19424461792022789560006241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12949641194681859706670827 19424461792022789560006241)
          ·
            refine ⟨14568346344017092170004681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19424461792022789560006241 14568346344017092170004681)
            ·
              refine ⟨10926259758012819127503511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14568346344017092170004681 10926259758012819127503511)
              ·
                refine ⟨16389389637019228691255267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10926259758012819127503511 16389389637019228691255267)
                ·
                  refine ⟨24584084455528843036882901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16389389637019228691255267 24584084455528843036882901)
                  ·
                    refine ⟨576189479426457258676943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24584084455528843036882901 576189479426457258676943)
                    ·
                      rfl

theorem cell23_3366375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3366375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366375 prefixEnd_3366375 := by exact prefixLift 3366375
  have htrace : WordTrace (prefixWord ++ tailWord_3366375) baseStart_3366375 baseEnd_3366375 := by
    simpa [prefixWord, tailWord_3366375, baseEnd_3366375] using wordTrace_append hprefix tailTrace_3366375
  have hstable : (prefixWord ++ tailWord_3366375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366375).length < 2 ^ (prefixWord ++ tailWord_3366375).sum := by decide
  have hdescent : baseEnd_3366375 < baseStart_3366375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366395 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4]
def baseStart_3366395 : Nat := 118140960795 + 3366395 * 2 ^ 59
def prefixEnd_3366395 : Nat := 4983230072969 + 3 ^ 40 * 3366395 * 2
def baseEnd_3366395 : Nat := 1728578707892461697780737

theorem tailTrace_3366395 : CollatzResearch.WordTrace tailWord_3366395 prefixEnd_3366395 1728578707892461697780737 := by
  unfold tailWord_3366395
  simp only [CollatzResearch.WordTrace]
  refine ⟨122782512639133324338236639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81855008426088882892157759 122782512639133324338236639)
  ·
    refine ⟨184173768958699986507354959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122782512639133324338236639 184173768958699986507354959)
    ·
      refine ⟨276260653438049979761032439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184173768958699986507354959 276260653438049979761032439)
      ·
        refine ⟨414390980157074969641548659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276260653438049979761032439 414390980157074969641548659)
        ·
          refine ⟨621586470235612454462322989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414390980157074969641548659 621586470235612454462322989)
          ·
            refine ⟨233094926338354670423371121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 621586470235612454462322989 233094926338354670423371121)
            ·
              refine ⟨174821194753766002817528341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233094926338354670423371121 174821194753766002817528341)
              ·
                refine ⟨8194743504082781382071641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174821194753766002817528341 8194743504082781382071641)
                ·
                  refine ⟨6146057628062086036553731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8194743504082781382071641 6146057628062086036553731)
                  ·
                    refine ⟨9219086442093129054830597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146057628062086036553731 9219086442093129054830597)
                    ·
                      refine ⟨1728578707892461697780737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9219086442093129054830597 1728578707892461697780737)
                      ·
                        rfl

theorem cell23_3366395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 1, 4].length) (baseStart_3366395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366395 prefixEnd_3366395 := by exact prefixLift 3366395
  have htrace : WordTrace (prefixWord ++ tailWord_3366395) baseStart_3366395 baseEnd_3366395 := by
    simpa [prefixWord, tailWord_3366395, baseEnd_3366395] using wordTrace_append hprefix tailTrace_3366395
  have hstable : (prefixWord ++ tailWord_3366395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366395).length < 2 ^ (prefixWord ++ tailWord_3366395).sum := by decide
  have hdescent : baseEnd_3366395 < baseStart_3366395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366402 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_3366402 : Nat := 118140960795 + 3366402 * 2 ^ 59
def prefixEnd_3366402 : Nat := 4983230072969 + 3 ^ 40 * 3366402 * 2
def baseEnd_3366402 : Nat := 1728582302257043170393205

theorem tailTrace_3366402 : CollatzResearch.WordTrace tailWord_3366402 prefixEnd_3366402 1728582302257043170393205 := by
  unfold tailWord_3366402
  simp only [CollatzResearch.WordTrace]
  refine ⟨30695691987526991133435365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81855178633405309689160973 30695691987526991133435365)
  ·
    refine ⟨5755442247661310837519131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30695691987526991133435365 5755442247661310837519131)
    ·
      refine ⟨8633163371491966256278697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5755442247661310837519131 8633163371491966256278697)
      ·
        refine ⟨6474872528618974692209023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8633163371491966256278697 6474872528618974692209023)
        ·
          refine ⟨9712308792928462038313535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6474872528618974692209023 9712308792928462038313535)
          ·
            refine ⟨14568463189392693057470303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9712308792928462038313535 14568463189392693057470303)
            ·
              refine ⟨21852694784089039586205455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14568463189392693057470303 21852694784089039586205455)
              ·
                refine ⟨32779042176133559379308183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21852694784089039586205455 32779042176133559379308183)
                ·
                  refine ⟨49168563264200339068962275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32779042176133559379308183 49168563264200339068962275)
                  ·
                    refine ⟨73752844896300508603443413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49168563264200339068962275 73752844896300508603443413)
                    ·
                      refine ⟨1728582302257043170393205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73752844896300508603443413 1728582302257043170393205)
                      ·
                        rfl

theorem cell23_3366402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_3366402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366402 prefixEnd_3366402 := by exact prefixLift 3366402
  have htrace : WordTrace (prefixWord ++ tailWord_3366402) baseStart_3366402 baseEnd_3366402 := by
    simpa [prefixWord, tailWord_3366402, baseEnd_3366402] using wordTrace_append hprefix tailTrace_3366402
  have hstable : (prefixWord ++ tailWord_3366402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366402).length < 2 ^ (prefixWord ++ tailWord_3366402).sum := by decide
  have hdescent : baseEnd_3366402 < baseStart_3366402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366456 : List Nat := [2, 1, 2, 1, 4, 2, 4, 2, 1, 4]
def baseStart_3366456 : Nat := 118140960795 + 3366456 * 2 ^ 59
def prefixEnd_3366456 : Nat := 4983230072969 + 3 ^ 40 * 3366456 * 2
def baseEnd_3366456 : Nat := 576203343404128653039319

theorem tailTrace_3366456 : CollatzResearch.WordTrace tailWord_3366456 prefixEnd_3366456 576203343404128653039319 := by
  unfold tailWord_3366456
  simp only [CollatzResearch.WordTrace]
  refine ⟨61392368745956165878103611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81856491661274887837471481 61392368745956165878103611)
  ·
    refine ⟨92088553118934248817155417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61392368745956165878103611 92088553118934248817155417)
    ·
      refine ⟨69066414839200686612866563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92088553118934248817155417 69066414839200686612866563)
      ·
        refine ⟨103599622258801029919299845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69066414839200686612866563 103599622258801029919299845)
        ·
          refine ⟨19424929173525193109868721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103599622258801029919299845 19424929173525193109868721)
          ·
            refine ⟨14568696880143894832401541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19424929173525193109868721 14568696880143894832401541)
            ·
              refine ⟨2731630665026980281075289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14568696880143894832401541 2731630665026980281075289)
              ·
                refine ⟨2048722998770235210806467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731630665026980281075289 2048722998770235210806467)
                ·
                  refine ⟨3073084498155352816209701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048722998770235210806467 3073084498155352816209701)
                  ·
                    refine ⟨576203343404128653039319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073084498155352816209701 576203343404128653039319)
                    ·
                      rfl

theorem cell23_3366456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_3366456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366456 prefixEnd_3366456 := by exact prefixLift 3366456
  have htrace : WordTrace (prefixWord ++ tailWord_3366456) baseStart_3366456 baseEnd_3366456 := by
    simpa [prefixWord, tailWord_3366456, baseEnd_3366456] using wordTrace_append hprefix tailTrace_3366456
  have hstable : (prefixWord ++ tailWord_3366456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366456).length < 2 ^ (prefixWord ++ tailWord_3366456).sum := by decide
  have hdescent : baseEnd_3366456 < baseStart_3366456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366482 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 3, 5]
def baseStart_3366482 : Nat := 118140960795 + 3366482 * 2 ^ 59
def prefixEnd_3366482 : Nat := 4983230072969 + 3 ^ 40 * 3366482 * 2
def baseEnd_3366482 : Nat := 576207793569800952464279

theorem tailTrace_3366482 : CollatzResearch.WordTrace tailWord_3366482 prefixEnd_3366482 576207793569800952464279 := by
  unfold tailWord_3366482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30696421447454534549163425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81857123859878758797769133 30696421447454534549163425)
  ·
    refine ⟨23022316085590900911872569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30696421447454534549163425 23022316085590900911872569)
    ·
      refine ⟨17266737064193175683904427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23022316085590900911872569 17266737064193175683904427)
      ·
        refine ⟨25900105596289763525856641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17266737064193175683904427 25900105596289763525856641)
        ·
          refine ⟨19425079197217322644392481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25900105596289763525856641 19425079197217322644392481)
          ·
            refine ⟨14568809397912991983294361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19425079197217322644392481 14568809397912991983294361)
            ·
              refine ⟨10926607048434743987470771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14568809397912991983294361 10926607048434743987470771)
              ·
                refine ⟨16389910572652115981206157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10926607048434743987470771 16389910572652115981206157)
                ·
                  refine ⟨6146216464744543492952309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16389910572652115981206157 6146216464744543492952309)
                  ·
                    refine ⟨576207793569800952464279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6146216464744543492952309 576207793569800952464279)
                    ·
                      rfl

theorem cell23_3366482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_3366482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366482 prefixEnd_3366482 := by exact prefixLift 3366482
  have htrace : WordTrace (prefixWord ++ tailWord_3366482) baseStart_3366482 baseEnd_3366482 := by
    simpa [prefixWord, tailWord_3366482, baseEnd_3366482] using wordTrace_append hprefix tailTrace_3366482
  have hstable : (prefixWord ++ tailWord_3366482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366482).length < 2 ^ (prefixWord ++ tailWord_3366482).sum := by decide
  have hdescent : baseEnd_3366482 < baseStart_3366482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366499 : List Nat := [1, 1, 1, 5, 1, 3, 4, 1, 1, 5]
def baseStart_3366499 : Nat := 118140960795 + 3366499 * 2 ^ 59
def prefixEnd_3366499 : Nat := 4983230072969 + 3 ^ 40 * 3366499 * 2
def baseEnd_3366499 : Nat := 576210703293509763626753

theorem tailTrace_3366499 : CollatzResearch.WordTrace tailWord_3366499 prefixEnd_3366499 576210703293509763626753 := by
  unfold tailWord_3366499
  simp only [CollatzResearch.WordTrace]
  refine ⟨122786305830756550100022551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81857537220504366733348367 122786305830756550100022551)
  ·
    refine ⟨184179458746134825150033827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122786305830756550100022551 184179458746134825150033827)
    ·
      refine ⟨276269188119202237725050741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184179458746134825150033827 276269188119202237725050741)
      ·
        refine ⟨25900236386175209786723507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 276269188119202237725050741 25900236386175209786723507)
        ·
          refine ⟨38850354579262814680085261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25900236386175209786723507 38850354579262814680085261)
          ·
            refine ⟨14568882967223555505031973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38850354579262814680085261 14568882967223555505031973)
            ·
              refine ⟨2731665556354416657193495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14568882967223555505031973 2731665556354416657193495)
              ·
                refine ⟨4097498334531624985790243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731665556354416657193495 4097498334531624985790243)
                ·
                  refine ⟨6146247501797437478685365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097498334531624985790243 6146247501797437478685365)
                  ·
                    refine ⟨576210703293509763626753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6146247501797437478685365 576210703293509763626753)
                    ·
                      rfl

theorem cell23_3366499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 4, 1, 1, 5].length) (baseStart_3366499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366499 prefixEnd_3366499 := by exact prefixLift 3366499
  have htrace : WordTrace (prefixWord ++ tailWord_3366499) baseStart_3366499 baseEnd_3366499 := by
    simpa [prefixWord, tailWord_3366499, baseEnd_3366499] using wordTrace_append hprefix tailTrace_3366499
  have hstable : (prefixWord ++ tailWord_3366499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366499).length < 2 ^ (prefixWord ++ tailWord_3366499).sum := by decide
  have hdescent : baseEnd_3366499 < baseStart_3366499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366522 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_3366522 : Nat := 118140960795 + 3366522 * 2 ^ 59
def prefixEnd_3366522 : Nat := 4983230072969 + 3 ^ 40 * 3366522 * 2
def baseEnd_3366522 : Nat := 1728643919935582700892653

theorem tailTrace_3366522 : CollatzResearch.WordTrace tailWord_3366522 prefixEnd_3366522 1728643919935582700892653 := by
  unfold tailWord_3366522
  simp only [CollatzResearch.WordTrace]
  refine ⟨30696786177418306257027455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81858096473115483352073213 30696786177418306257027455)
  ·
    refine ⟨46045179266127459385541183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30696786177418306257027455 46045179266127459385541183)
    ·
      refine ⟨69067768899191189078311775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46045179266127459385541183 69067768899191189078311775)
      ·
        refine ⟨103601653348786783617467663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69067768899191189078311775 103601653348786783617467663)
        ·
          refine ⟨155402480023180175426201495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103601653348786783617467663 155402480023180175426201495)
          ·
            refine ⟨233103720034770263139302243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155402480023180175426201495 233103720034770263139302243)
            ·
              refine ⟨349655580052155394708953365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233103720034770263139302243 349655580052155394708953365)
              ·
                refine ⟨16390105314944784126982189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 349655580052155394708953365 16390105314944784126982189)
                ·
                  refine ⟨6146289493104294047618321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16390105314944784126982189 6146289493104294047618321)
                  ·
                    refine ⟨4609717119828220535713741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6146289493104294047618321 4609717119828220535713741)
                    ·
                      refine ⟨1728643919935582700892653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609717119828220535713741 1728643919935582700892653)
                      ·
                        rfl

theorem cell23_3366522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_3366522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366522 prefixEnd_3366522 := by exact prefixLift 3366522
  have htrace : WordTrace (prefixWord ++ tailWord_3366522) baseStart_3366522 baseEnd_3366522 := by
    simpa [prefixWord, tailWord_3366522, baseEnd_3366522] using wordTrace_append hprefix tailTrace_3366522
  have hstable : (prefixWord ++ tailWord_3366522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366522).length < 2 ^ (prefixWord ++ tailWord_3366522).sum := by decide
  have hdescent : baseEnd_3366522 < baseStart_3366522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366529 : List Nat := [1, 2, 4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3366529 : Nat := 118140960795 + 3366529 * 2 ^ 59
def prefixEnd_3366529 : Nat := 4983230072969 + 3 ^ 40 * 3366529 * 2
def baseEnd_3366529 : Nat := 576215838100054724501707

theorem tailTrace_3366529 : CollatzResearch.WordTrace tailWord_3366529 prefixEnd_3366529 576215838100054724501707 := by
  unfold tailWord_3366529
  simp only [CollatzResearch.WordTrace]
  refine ⟨122787400020647865223614641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81858266680431910149076427 122787400020647865223614641)
  ·
    refine ⟨92090550015485898917710981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122787400020647865223614641 92090550015485898917710981)
    ·
      refine ⟨17266978127903606047070809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92090550015485898917710981 17266978127903606047070809)
      ·
        refine ⟨12950233595927704535303107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17266978127903606047070809 12950233595927704535303107)
        ·
          refine ⟨19425350393891556802954661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12950233595927704535303107 19425350393891556802954661)
          ·
            refine ⟨3642253198854666900553999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19425350393891556802954661 3642253198854666900553999)
            ·
              refine ⟨5463379798282000350830999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642253198854666900553999 5463379798282000350830999)
              ·
                refine ⟨8195069697423000526246499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463379798282000350830999 8195069697423000526246499)
                ·
                  refine ⟨12292604546134500789369749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195069697423000526246499 12292604546134500789369749)
                  ·
                    refine ⟨576215838100054724501707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12292604546134500789369749 576215838100054724501707)
                    ·
                      rfl

theorem cell23_3366529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3366529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366529 prefixEnd_3366529 := by exact prefixLift 3366529
  have htrace : WordTrace (prefixWord ++ tailWord_3366529) baseStart_3366529 baseEnd_3366529 := by
    simpa [prefixWord, tailWord_3366529, baseEnd_3366529] using wordTrace_append hprefix tailTrace_3366529
  have hstable : (prefixWord ++ tailWord_3366529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366529).length < 2 ^ (prefixWord ++ tailWord_3366529).sum := by decide
  have hdescent : baseEnd_3366529 < baseStart_3366529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366539 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 3]
def baseStart_3366539 : Nat := 118140960795 + 3366539 * 2 ^ 59
def prefixEnd_3366539 : Nat := 4983230072969 + 3 ^ 40 * 3366539 * 2
def baseEnd_3366539 : Nat := 1728652649106709134380075

theorem tailTrace_3366539 : CollatzResearch.WordTrace tailWord_3366539 prefixEnd_3366539 1728652649106709134380075 := by
  unfold tailWord_3366539
  simp only [CollatzResearch.WordTrace]
  refine ⟨122787764750611636931478671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81858509833741091287652447 122787764750611636931478671)
  ·
    refine ⟨184181647125917455397218007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122787764750611636931478671 184181647125917455397218007)
    ·
      refine ⟨276272470688876183095827011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184181647125917455397218007 276272470688876183095827011)
      ·
        refine ⟨414408706033314274643740517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276272470688876183095827011 414408706033314274643740517)
        ·
          refine ⟨77701632381246426495701347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 414408706033314274643740517 77701632381246426495701347)
          ·
            refine ⟨116552448571869639743552021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77701632381246426495701347 116552448571869639743552021)
            ·
              refine ⟨5463396026806389362979001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116552448571869639743552021 5463396026806389362979001)
              ·
                refine ⟨4097547020104792022234251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463396026806389362979001 4097547020104792022234251)
                ·
                  refine ⟨6146320530157188033351377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4097547020104792022234251 6146320530157188033351377)
                  ·
                    refine ⟨4609740397617891025013533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6146320530157188033351377 4609740397617891025013533)
                    ·
                      refine ⟨1728652649106709134380075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609740397617891025013533 1728652649106709134380075)
                      ·
                        rfl

theorem cell23_3366539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 1, 2, 3].length) (baseStart_3366539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366539 prefixEnd_3366539 := by exact prefixLift 3366539
  have htrace : WordTrace (prefixWord ++ tailWord_3366539) baseStart_3366539 baseEnd_3366539 := by
    simpa [prefixWord, tailWord_3366539, baseEnd_3366539] using wordTrace_append hprefix tailTrace_3366539
  have hstable : (prefixWord ++ tailWord_3366539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366539).length < 2 ^ (prefixWord ++ tailWord_3366539).sum := by decide
  have hdescent : baseEnd_3366539 < baseStart_3366539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366542 : List Nat := [4, 1, 1, 3, 1, 3, 1, 9]
def baseStart_3366542 : Nat := 118140960795 + 3366542 * 2 ^ 59
def prefixEnd_3366542 : Nat := 4983230072969 + 3 ^ 40 * 3366542 * 2
def baseEnd_3366542 : Nat := 64024229242543430468243

theorem tailTrace_3366542 : CollatzResearch.WordTrace tailWord_3366542 prefixEnd_3366542 64024229242543430468243 := by
  unfold tailWord_3366542
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348484271200096055479735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81858582779733845629225253 15348484271200096055479735)
  ·
    refine ⟨23022726406800144083219603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15348484271200096055479735 23022726406800144083219603)
    ·
      refine ⟨34534089610200216124829405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23022726406800144083219603 34534089610200216124829405)
      ·
        refine ⟨12950283603825081046811027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34534089610200216124829405 12950283603825081046811027)
        ·
          refine ⟨19425425405737621570216541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12950283603825081046811027 19425425405737621570216541)
          ·
            refine ⟨7284534527151608088831203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19425425405737621570216541 7284534527151608088831203)
            ·
              refine ⟨10926801790727412133246805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284534527151608088831203 10926801790727412133246805)
              ·
                refine ⟨64024229242543430468243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10926801790727412133246805 64024229242543430468243)
                ·
                  rfl

theorem cell23_3366542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 9].length) (baseStart_3366542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366542 prefixEnd_3366542 := by exact prefixLift 3366542
  have htrace : WordTrace (prefixWord ++ tailWord_3366542) baseStart_3366542 baseEnd_3366542 := by
    simpa [prefixWord, tailWord_3366542, baseEnd_3366542] using wordTrace_append hprefix tailTrace_3366542
  have hstable : (prefixWord ++ tailWord_3366542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366542).length < 2 ^ (prefixWord ++ tailWord_3366542).sum := by decide
  have hdescent : baseEnd_3366542 < baseStart_3366542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366559 : List Nat := [1, 1, 2, 7, 1, 2, 9]
def baseStart_3366559 : Nat := 118140960795 + 3366559 * 2 ^ 59
def prefixEnd_3366559 : Nat := 4983230072969 + 3 ^ 40 * 3366559 * 2
def baseEnd_3366559 : Nat := 21341517515059247606543

theorem tailTrace_3366559 : CollatzResearch.WordTrace tailWord_3366559 prefixEnd_3366559 21341517515059247606543 := by
  unfold tailWord_3366559
  simp only [CollatzResearch.WordTrace]
  refine ⟨122788494210539180347206731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81858996140359453564804487 122788494210539180347206731)
  ·
    refine ⟨184182741315808770520810097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122788494210539180347206731 184182741315808770520810097)
    ·
      refine ⟨138137055986856577890607573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184182741315808770520810097 138137055986856577890607573)
      ·
        refine ⟨3237587249691951044311115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 138137055986856577890607573 3237587249691951044311115)
        ·
          refine ⟨4856380874537926566466673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237587249691951044311115 4856380874537926566466673)
          ·
            refine ⟨3642285655903444924850005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4856380874537926566466673 3642285655903444924850005)
            ·
              refine ⟨21341517515059247606543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3642285655903444924850005 21341517515059247606543)
              ·
                rfl

theorem cell23_3366559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 9].length) (baseStart_3366559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366559 prefixEnd_3366559 := by exact prefixLift 3366559
  have htrace : WordTrace (prefixWord ++ tailWord_3366559) baseStart_3366559 baseEnd_3366559 := by
    simpa [prefixWord, tailWord_3366559, baseEnd_3366559] using wordTrace_append hprefix tailTrace_3366559
  have hstable : (prefixWord ++ tailWord_3366559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366559).length < 2 ^ (prefixWord ++ tailWord_3366559).sum := by decide
  have hdescent : baseEnd_3366559 < baseStart_3366559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366579 : List Nat := [1, 1, 1, 2, 3, 3, 2, 2, 3, 3, 2]
def baseStart_3366579 : Nat := 118140960795 + 3366579 * 2 ^ 59
def prefixEnd_3366579 : Nat := 4983230072969 + 3 ^ 40 * 3366579 * 2
def baseEnd_3366579 : Nat := 1728673188332888977879891

theorem tailTrace_3366579 : CollatzResearch.WordTrace tailWord_3366579 prefixEnd_3366579 1728673188332888977879891 := by
  unfold tailWord_3366579
  simp only [CollatzResearch.WordTrace]
  refine ⟨122789223670466723762934791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81859482446977815841956527 122789223670466723762934791)
  ·
    refine ⟨184183835505700085644402187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122789223670466723762934791 184183835505700085644402187)
    ·
      refine ⟨276275753258550128466603281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184183835505700085644402187 276275753258550128466603281)
      ·
        refine ⟨207206814943912596349952461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276275753258550128466603281 207206814943912596349952461)
        ·
          refine ⟨77702555603967223631232173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207206814943912596349952461 77702555603967223631232173)
          ·
            refine ⟨29138458351487708861712065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77702555603967223631232173 29138458351487708861712065)
            ·
              refine ⟨21853843763615781646284049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29138458351487708861712065 21853843763615781646284049)
              ·
                refine ⟨16390382822711836234713037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21853843763615781646284049 16390382822711836234713037)
                ·
                  refine ⟨6146393558516938588017389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16390382822711836234713037 6146393558516938588017389)
                  ·
                    refine ⟨2304897584443851970506521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6146393558516938588017389 2304897584443851970506521)
                    ·
                      refine ⟨1728673188332888977879891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304897584443851970506521 1728673188332888977879891)
                      ·
                        rfl

theorem cell23_3366579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 3, 3, 2].length) (baseStart_3366579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366579 prefixEnd_3366579 := by exact prefixLift 3366579
  have htrace : WordTrace (prefixWord ++ tailWord_3366579) baseStart_3366579 baseEnd_3366579 := by
    simpa [prefixWord, tailWord_3366579, baseEnd_3366579] using wordTrace_append hprefix tailTrace_3366579
  have hstable : (prefixWord ++ tailWord_3366579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366579).length < 2 ^ (prefixWord ++ tailWord_3366579).sum := by decide
  have hdescent : baseEnd_3366579 < baseStart_3366579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366586 : List Nat := [3, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_3366586 : Nat := 118140960795 + 3366586 * 2 ^ 59
def prefixEnd_3366586 : Nat := 4983230072969 + 3 ^ 40 * 3366586 * 2
def baseEnd_3366586 : Nat := 1728676782697470450492359

theorem tailTrace_3366586 : CollatzResearch.WordTrace tailWord_3366586 prefixEnd_3366586 1728676782697470450492359 := by
  unfold tailWord_3366586
  simp only [CollatzResearch.WordTrace]
  refine ⟨30697369745360340989609903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81859652654294242638959741 30697369745360340989609903)
  ·
    refine ⟨46046054618040511484414855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30697369745360340989609903 46046054618040511484414855)
    ·
      refine ⟨69069081927060767226622283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46046054618040511484414855 69069081927060767226622283)
      ·
        refine ⟨103603622890591150839933425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69069081927060767226622283 103603622890591150839933425)
        ·
          refine ⟨77702717167943363129950069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103603622890591150839933425 77702717167943363129950069)
          ·
            refine ⟨7284629734494690293432819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77702717167943363129950069 7284629734494690293432819)
            ·
              refine ⟨10926944601742035440149229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284629734494690293432819 10926944601742035440149229)
              ·
                refine ⟨4097604225653263290055961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10926944601742035440149229 4097604225653263290055961)
                ·
                  refine ⟨3073203169239947467541971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4097604225653263290055961 3073203169239947467541971)
                  ·
                    refine ⟨4609804753859921201312957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3073203169239947467541971 4609804753859921201312957)
                    ·
                      refine ⟨1728676782697470450492359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609804753859921201312957 1728676782697470450492359)
                      ·
                        rfl

theorem cell23_3366586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_3366586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366586 prefixEnd_3366586 := by exact prefixLift 3366586
  have htrace : WordTrace (prefixWord ++ tailWord_3366586) baseStart_3366586 baseEnd_3366586 := by
    simpa [prefixWord, tailWord_3366586, baseEnd_3366586] using wordTrace_append hprefix tailTrace_3366586
  have hstable : (prefixWord ++ tailWord_3366586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366586).length < 2 ^ (prefixWord ++ tailWord_3366586).sum := by decide
  have hdescent : baseEnd_3366586 < baseStart_3366586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366595 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9]
def baseStart_3366595 : Nat := 118140960795 + 3366595 * 2 ^ 59
def prefixEnd_3366595 : Nat := 4983230072969 + 3 ^ 40 * 3366595 * 2
def baseEnd_3366595 : Nat := 1728681404023360915279817

theorem tailTrace_3366595 : CollatzResearch.WordTrace tailWord_3366595 prefixEnd_3366595 1728681404023360915279817 := by
  unfold tailWord_3366595
  simp only [CollatzResearch.WordTrace]
  refine ⟨122789807238408758495517239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81859871492272505663678159 122789807238408758495517239)
  ·
    refine ⟨184184710857613137743275859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122789807238408758495517239 184184710857613137743275859)
    ·
      refine ⟨276277066286419706614913789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184184710857613137743275859 276277066286419706614913789)
      ·
        refine ⟨103603899857407389980592671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276277066286419706614913789 103603899857407389980592671)
        ·
          refine ⟨155405849786111084970889007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103603899857407389980592671 155405849786111084970889007)
          ·
            refine ⟨233108774679166627456333511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155405849786111084970889007 233108774679166627456333511)
            ·
              refine ⟨349663162018749941184500267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233108774679166627456333511 349663162018749941184500267)
              ·
                refine ⟨524494743028124911776750401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349663162018749941184500267 524494743028124911776750401)
                ·
                  refine ⟨393371057271093683832562801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 524494743028124911776750401 393371057271093683832562801)
                  ·
                    refine ⟨295028292953320262874422101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 393371057271093683832562801 295028292953320262874422101)
                    ·
                      refine ⟨1728681404023360915279817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 295028292953320262874422101 1728681404023360915279817)
                      ·
                        rfl

theorem cell23_3366595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_3366595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366595 prefixEnd_3366595 := by exact prefixLift 3366595
  have htrace : WordTrace (prefixWord ++ tailWord_3366595) baseStart_3366595 baseEnd_3366595 := by
    simpa [prefixWord, tailWord_3366595, baseEnd_3366595] using wordTrace_append hprefix tailTrace_3366595
  have hstable : (prefixWord ++ tailWord_3366595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366595).length < 2 ^ (prefixWord ++ tailWord_3366595).sum := by decide
  have hdescent : baseEnd_3366595 < baseStart_3366595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366596 : List Nat := [2, 3, 3, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_3366596 : Nat := 118140960795 + 3366596 * 2 ^ 59
def prefixEnd_3366596 : Nat := 4983230072969 + 3 ^ 40 * 3366596 * 2
def baseEnd_3366596 : Nat := 1728681917504015411367313

theorem tailTrace_3366596 : CollatzResearch.WordTrace tailWord_3366596 prefixEnd_3366596 1728681917504015411367313 := by
  unfold tailWord_3366596
  simp only [CollatzResearch.WordTrace]
  refine ⟨61394921855702567833151821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81859895807603423777535761 61394921855702567833151821)
  ·
    refine ⟨23023095695888462937431933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61394921855702567833151821 23023095695888462937431933)
    ·
      refine ⟨8633660885958173601536975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23023095695888462937431933 8633660885958173601536975)
      ·
        refine ⟨12950491328937260402305463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8633660885958173601536975 12950491328937260402305463)
        ·
          refine ⟨19425736993405890603458195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12950491328937260402305463 19425736993405890603458195)
          ·
            refine ⟨29138605490108835905187293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19425736993405890603458195 29138605490108835905187293)
            ·
              refine ⟨10926977058790813464445235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29138605490108835905187293 10926977058790813464445235)
              ·
                refine ⟨16390465588186220196667853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10926977058790813464445235 16390465588186220196667853)
                ·
                  refine ⟨6146424595569832573750445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16390465588186220196667853 6146424595569832573750445)
                  ·
                    refine ⟨2304909223338687215156417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6146424595569832573750445 2304909223338687215156417)
                    ·
                      refine ⟨1728681917504015411367313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304909223338687215156417 1728681917504015411367313)
                      ·
                        rfl

theorem cell23_3366596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_3366596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366596 prefixEnd_3366596 := by exact prefixLift 3366596
  have htrace : WordTrace (prefixWord ++ tailWord_3366596) baseStart_3366596 baseEnd_3366596 := by
    simpa [prefixWord, tailWord_3366596, baseEnd_3366596] using wordTrace_append hprefix tailTrace_3366596
  have hstable : (prefixWord ++ tailWord_3366596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366596).length < 2 ^ (prefixWord ++ tailWord_3366596).sum := by decide
  have hdescent : baseEnd_3366596 < baseStart_3366596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366609 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 3, 4, 2]
def baseStart_3366609 : Nat := 118140960795 + 3366609 * 2 ^ 59
def prefixEnd_3366609 : Nat := 4983230072969 + 3 ^ 40 * 3366609 * 2
def baseEnd_3366609 : Nat := 1728688592752523860504753

theorem tailTrace_3366609 : CollatzResearch.WordTrace tailWord_3366609 prefixEnd_3366609 1728688592752523860504753 := by
  unfold tailWord_3366609
  simp only [CollatzResearch.WordTrace]
  refine ⟨122790317860358038886526881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81860211906905359257684587 122790317860358038886526881)
  ·
    refine ⟨92092738395268529164895161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122790317860358038886526881 92092738395268529164895161)
    ·
      refine ⟨69069553796451396873671371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92092738395268529164895161 69069553796451396873671371)
      ·
        refine ⟨103604330694677095310507057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69069553796451396873671371 103604330694677095310507057)
        ·
          refine ⟨77703248021007821482880293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103604330694677095310507057 77703248021007821482880293)
          ·
            refine ⟨14569359003938966528040055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77703248021007821482880293 14569359003938966528040055)
            ·
              refine ⟨21854038505908449792060083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14569359003938966528040055 21854038505908449792060083)
              ·
                refine ⟨32781057758862674688090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21854038505908449792060083 32781057758862674688090125)
                ·
                  refine ⟨12292896659573503008033797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32781057758862674688090125 12292896659573503008033797)
                  ·
                    refine ⟨2304918123670031814006337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12292896659573503008033797 2304918123670031814006337)
                    ·
                      refine ⟨1728688592752523860504753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304918123670031814006337 1728688592752523860504753)
                      ·
                        rfl

theorem cell23_3366609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 4, 2].length) (baseStart_3366609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366609 prefixEnd_3366609 := by exact prefixLift 3366609
  have htrace : WordTrace (prefixWord ++ tailWord_3366609) baseStart_3366609 baseEnd_3366609 := by
    simpa [prefixWord, tailWord_3366609, baseEnd_3366609] using wordTrace_append hprefix tailTrace_3366609
  have hstable : (prefixWord ++ tailWord_3366609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366609).length < 2 ^ (prefixWord ++ tailWord_3366609).sum := by decide
  have hdescent : baseEnd_3366609 < baseStart_3366609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366620 : List Nat := [2, 2, 5, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_3366620 : Nat := 118140960795 + 3366620 * 2 ^ 59
def prefixEnd_3366620 : Nat := 4983230072969 + 3 ^ 40 * 3366620 * 2
def baseEnd_3366620 : Nat := 1728694241039723317467203

theorem tailTrace_3366620 : CollatzResearch.WordTrace tailWord_3366620 prefixEnd_3366620 1728694241039723317467203 := by
  unfold tailWord_3366620
  simp only [CollatzResearch.WordTrace]
  refine ⟨61395359531659093882588657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81860479375545458510118209 61395359531659093882588657)
  ·
    refine ⟨46046519648744320411941493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61395359531659093882588657 46046519648744320411941493)
    ·
      refine ⟨4316861217069780038619515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46046519648744320411941493 4316861217069780038619515)
      ·
        refine ⟨6475291825604670057929273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316861217069780038619515 6475291825604670057929273)
        ·
          refine ⟨4856468869203502543446955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6475291825604670057929273 4856468869203502543446955)
          ·
            refine ⟨7284703303805253815170433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856468869203502543446955 7284703303805253815170433)
            ·
              refine ⟨5463527477853940361377825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284703303805253815170433 5463527477853940361377825)
              ·
                refine ⟨4097645608390455271033369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5463527477853940361377825 4097645608390455271033369)
                ·
                  refine ⟨3073234206292841453275027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4097645608390455271033369 3073234206292841453275027)
                  ·
                    refine ⟨4609851309439262179912541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3073234206292841453275027 4609851309439262179912541)
                    ·
                      refine ⟨1728694241039723317467203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4609851309439262179912541 1728694241039723317467203)
                      ·
                        rfl

theorem cell23_3366620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_3366620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366620 prefixEnd_3366620 := by exact prefixLift 3366620
  have htrace : WordTrace (prefixWord ++ tailWord_3366620) baseStart_3366620 baseEnd_3366620 := by
    simpa [prefixWord, tailWord_3366620, baseEnd_3366620] using wordTrace_append hprefix tailTrace_3366620
  have hstable : (prefixWord ++ tailWord_3366620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366620).length < 2 ^ (prefixWord ++ tailWord_3366620).sum := by decide
  have hdescent : baseEnd_3366620 < baseStart_3366620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366621 : List Nat := [1, 4, 3, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_3366621 : Nat := 118140960795 + 3366621 * 2 ^ 59
def prefixEnd_3366621 : Nat := 4983230072969 + 3 ^ 40 * 3366621 * 2
def baseEnd_3366621 : Nat := 1728694754520377813554699

theorem tailTrace_3366621 : CollatzResearch.WordTrace tailWord_3366621 prefixEnd_3366621 1728694754520377813554699 := by
  unfold tailWord_3366621
  simp only [CollatzResearch.WordTrace]
  refine ⟨122790755536314564935963717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81860503690876376623975811 122790755536314564935963717)
  ·
    refine ⟨23023266663058980925493197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122790755536314564935963717 23023266663058980925493197)
    ·
      refine ⟨8633724998647117847059949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23023266663058980925493197 8633724998647117847059949)
      ·
        refine ⟨3237646874492669192647481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8633724998647117847059949 3237646874492669192647481)
        ·
          refine ⟨2428235155869501894485611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3237646874492669192647481 2428235155869501894485611)
          ·
            refine ⟨3642352733804252841728417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428235155869501894485611 3642352733804252841728417)
            ·
              refine ⟨2731764550353189631296313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642352733804252841728417 2731764550353189631296313)
              ·
                refine ⟨2048823412764892223472235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731764550353189631296313 2048823412764892223472235)
                ·
                  refine ⟨3073235119147338335208353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048823412764892223472235 3073235119147338335208353)
                  ·
                    refine ⟨2304926339360503751406265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3073235119147338335208353 2304926339360503751406265)
                    ·
                      refine ⟨1728694754520377813554699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304926339360503751406265 1728694754520377813554699)
                      ·
                        rfl

theorem cell23_3366621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_3366621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366621 prefixEnd_3366621 := by exact prefixLift 3366621
  have htrace : WordTrace (prefixWord ++ tailWord_3366621) baseStart_3366621 baseEnd_3366621 := by
    simpa [prefixWord, tailWord_3366621, baseEnd_3366621] using wordTrace_append hprefix tailTrace_3366621
  have hstable : (prefixWord ++ tailWord_3366621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366621).length < 2 ^ (prefixWord ++ tailWord_3366621).sum := by decide
  have hdescent : baseEnd_3366621 < baseStart_3366621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366666 : List Nat := [3, 1, 2, 2, 1, 4, 2, 3, 5]
def baseStart_3366666 : Nat := 118140960795 + 3366666 * 2 ^ 59
def prefixEnd_3366666 : Nat := 4983230072969 + 3 ^ 40 * 3366666 * 2
def baseEnd_3366666 : Nat := 192079762349981126387999

theorem tailTrace_3366666 : CollatzResearch.WordTrace tailWord_3366666 prefixEnd_3366666 192079762349981126387999 := by
  unfold tailWord_3366666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30698099205287884405337963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81861597880767691747567901 30698099205287884405337963)
  ·
    refine ⟨46047148807931826608006945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30698099205287884405337963 46047148807931826608006945)
    ·
      refine ⟨34535361605948869956005209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46047148807931826608006945 34535361605948869956005209)
      ·
        refine ⟨25901521204461652467003907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34535361605948869956005209 25901521204461652467003907)
        ·
          refine ⟨38852281806692478700505861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25901521204461652467003907 38852281806692478700505861)
          ·
            refine ⟨7284802838754839756344849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38852281806692478700505861 7284802838754839756344849)
            ·
              refine ⟨5463602129066129817258637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284802838754839756344849 5463602129066129817258637)
              ·
                refine ⟨2048850798399798681471989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463602129066129817258637 2048850798399798681471989)
                ·
                  refine ⟨192079762349981126387999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2048850798399798681471989 192079762349981126387999)
                  ·
                    rfl

theorem cell23_3366666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 3, 5].length) (baseStart_3366666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366666 prefixEnd_3366666 := by exact prefixLift 3366666
  have htrace : WordTrace (prefixWord ++ tailWord_3366666) baseStart_3366666 baseEnd_3366666 := by
    simpa [prefixWord, tailWord_3366666, baseEnd_3366666] using wordTrace_append hprefix tailTrace_3366666
  have hstable : (prefixWord ++ tailWord_3366666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366666).length < 2 ^ (prefixWord ++ tailWord_3366666).sum := by decide
  have hdescent : baseEnd_3366666 < baseStart_3366666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366699 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 6, 4, 2]
def baseStart_3366699 : Nat := 118140960795 + 3366699 * 2 ^ 59
def prefixEnd_3366699 : Nat := 4983230072969 + 3 ^ 40 * 3366699 * 2
def baseEnd_3366699 : Nat := 1728734806011428508379339

theorem tailTrace_3366699 : CollatzResearch.WordTrace tailWord_3366699 prefixEnd_3366699 1728734806011428508379339 := by
  unfold tailWord_3366699
  simp only [CollatzResearch.WordTrace]
  refine ⟨122793600430031984257303151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81862400286687989504868767 122793600430031984257303151)
  ·
    refine ⟨184190400645047976385954727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122793600430031984257303151 184190400645047976385954727)
    ·
      refine ⟨276285600967571964578932091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184190400645047976385954727 276285600967571964578932091)
      ·
        refine ⟨414428401451357946868398137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276285600967571964578932091 414428401451357946868398137)
        ·
          refine ⟨310821301088518460151298603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414428401451357946868398137 310821301088518460151298603)
          ·
            refine ⟨466231951632777690226947905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310821301088518460151298603 466231951632777690226947905)
            ·
              refine ⟨349673963724583267670210929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466231951632777690226947905 349673963724583267670210929)
              ·
                refine ⟨262255472793437450752658197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349673963724583267670210929 262255472793437450752658197)
                ·
                  refine ⟨12293225287192380504030853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 262255472793437450752658197 12293225287192380504030853)
                  ·
                    refine ⟨2304979741348571344505785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12293225287192380504030853 2304979741348571344505785)
                    ·
                      refine ⟨1728734806011428508379339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2304979741348571344505785 1728734806011428508379339)
                      ·
                        rfl

theorem cell23_3366699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 6, 4, 2].length) (baseStart_3366699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366699 prefixEnd_3366699 := by exact prefixLift 3366699
  have htrace : WordTrace (prefixWord ++ tailWord_3366699) baseStart_3366699 baseEnd_3366699 := by
    simpa [prefixWord, tailWord_3366699, baseEnd_3366699] using wordTrace_append hprefix tailTrace_3366699
  have hstable : (prefixWord ++ tailWord_3366699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366699).length < 2 ^ (prefixWord ++ tailWord_3366699).sum := by decide
  have hdescent : baseEnd_3366699 < baseStart_3366699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366733 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_3366733 : Nat := 118140960795 + 3366733 * 2 ^ 59
def prefixEnd_3366733 : Nat := 4983230072969 + 3 ^ 40 * 3366733 * 2
def baseEnd_3366733 : Nat := 1728752264353681375354183

theorem tailTrace_3366733 : CollatzResearch.WordTrace tailWord_3366733 prefixEnd_3366733 1728752264353681375354183 := by
  unfold tailWord_3366733
  simp only [CollatzResearch.WordTrace]
  refine ⟨122794840511908808064040853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81863227007939205376027235 122794840511908808064040853)
  ·
    refine ⟨5756008148995725378001915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122794840511908808064040853 5756008148995725378001915)
    ·
      refine ⟨8634012223493588067002873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5756008148995725378001915 8634012223493588067002873)
      ·
        refine ⟨6475509167620191050252155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8634012223493588067002873 6475509167620191050252155)
        ·
          refine ⟨9713263751430286575378233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6475509167620191050252155 9713263751430286575378233)
          ·
            refine ⟨7284947813572714931533675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9713263751430286575378233 7284947813572714931533675)
            ·
              refine ⟨10927421720359072397300513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284947813572714931533675 10927421720359072397300513)
              ·
                refine ⟨8195566290269304297975385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10927421720359072397300513 8195566290269304297975385)
                ·
                  refine ⟨6146674717701978223481539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8195566290269304297975385 6146674717701978223481539)
                  ·
                    refine ⟨9220012076552967335222309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6146674717701978223481539 9220012076552967335222309)
                    ·
                      refine ⟨1728752264353681375354183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9220012076552967335222309 1728752264353681375354183)
                      ·
                        rfl

theorem cell23_3366733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_3366733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366733 prefixEnd_3366733 := by exact prefixLift 3366733
  have htrace : WordTrace (prefixWord ++ tailWord_3366733) baseStart_3366733 baseEnd_3366733 := by
    simpa [prefixWord, tailWord_3366733, baseEnd_3366733] using wordTrace_append hprefix tailTrace_3366733
  have hstable : (prefixWord ++ tailWord_3366733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366733).length < 2 ^ (prefixWord ++ tailWord_3366733).sum := by decide
  have hdescent : baseEnd_3366733 < baseStart_3366733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366743 : List Nat := [1, 1, 3, 2, 5, 2, 1, 1, 3, 4]
def baseStart_3366743 : Nat := 118140960795 + 3366743 * 2 ^ 59
def prefixEnd_3366743 : Nat := 4983230072969 + 3 ^ 40 * 3366743 * 2
def baseEnd_3366743 : Nat := 576252466386742112076379

theorem tailTrace_3366743 : CollatzResearch.WordTrace tailWord_3366743 prefixEnd_3366743 576252466386742112076379 := by
  unfold tailWord_3366743
  simp only [CollatzResearch.WordTrace]
  refine ⟨122795205241872579771904883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81863470161248386514603255 122795205241872579771904883)
  ·
    refine ⟨184192807862808869657857325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122795205241872579771904883 184192807862808869657857325)
    ·
      refine ⟨69072302948553326121696497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184192807862808869657857325 69072302948553326121696497)
      ·
        refine ⟨51804227211414994591272373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69072302948553326121696497 51804227211414994591272373)
        ·
          refine ⟨4856646301070155742931785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51804227211414994591272373 4856646301070155742931785)
          ·
            refine ⟨3642484725802616807198839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4856646301070155742931785 3642484725802616807198839)
            ·
              refine ⟨5463727088703925210798259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642484725802616807198839 5463727088703925210798259)
              ·
                refine ⟨8195590633055887816197389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5463727088703925210798259 8195590633055887816197389)
                ·
                  refine ⟨3073346487395957931074021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8195590633055887816197389 3073346487395957931074021)
                  ·
                    refine ⟨576252466386742112076379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073346487395957931074021 576252466386742112076379)
                    ·
                      rfl

theorem cell23_3366743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_3366743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366743 prefixEnd_3366743 := by exact prefixLift 3366743
  have htrace : WordTrace (prefixWord ++ tailWord_3366743) baseStart_3366743 baseEnd_3366743 := by
    simpa [prefixWord, tailWord_3366743, baseEnd_3366743] using wordTrace_append hprefix tailTrace_3366743
  have hstable : (prefixWord ++ tailWord_3366743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366743).length < 2 ^ (prefixWord ++ tailWord_3366743).sum := by decide
  have hdescent : baseEnd_3366743 < baseStart_3366743 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366756 : List Nat := [2, 3, 1, 1, 5, 1, 1, 3, 6]
def baseStart_3366756 : Nat := 118140960795 + 3366756 * 2 ^ 59
def prefixEnd_3366756 : Nat := 4983230072969 + 3 ^ 40 * 3366756 * 2
def baseEnd_3366756 : Nat := 192084897156526087262953

theorem tailTrace_3366756 : CollatzResearch.WordTrace tailWord_3366756 prefixEnd_3366756 192084897156526087262953 := by
  unfold tailWord_3366756
  simp only [CollatzResearch.WordTrace]
  refine ⟨61397839695412741496064061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81863786260550321994752081 61397839695412741496064061)
  ·
    refine ⟨23024189885779778061024023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61397839695412741496064061 23024189885779778061024023)
    ·
      refine ⟨34536284828669667091536035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23024189885779778061024023 34536284828669667091536035)
      ·
        refine ⟨51804427243004500637304053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34536284828669667091536035 51804427243004500637304053)
        ·
          refine ⟨4856665054031671934747255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51804427243004500637304053 4856665054031671934747255)
          ·
            refine ⟨7284997581047507902120883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4856665054031671934747255 7284997581047507902120883)
            ·
              refine ⟨10927496371571261853181325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7284997581047507902120883 10927496371571261853181325)
              ·
                refine ⟨4097811139339223194942997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10927496371571261853181325 4097811139339223194942997)
                ·
                  refine ⟨192084897156526087262953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4097811139339223194942997 192084897156526087262953)
                  ·
                    rfl

theorem cell23_3366756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_3366756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366756 prefixEnd_3366756 := by exact prefixLift 3366756
  have htrace : WordTrace (prefixWord ++ tailWord_3366756) baseStart_3366756 baseEnd_3366756 := by
    simpa [prefixWord, tailWord_3366756, baseEnd_3366756] using wordTrace_append hprefix tailTrace_3366756
  have hstable : (prefixWord ++ tailWord_3366756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366756).length < 2 ^ (prefixWord ++ tailWord_3366756).sum := by decide
  have hdescent : baseEnd_3366756 < baseStart_3366756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366769 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_3366769 : Nat := 118140960795 + 3366769 * 2 ^ 59
def prefixEnd_3366769 : Nat := 4983230072969 + 3 ^ 40 * 3366769 * 2
def baseEnd_3366769 : Nat := 576256916552414411501339

theorem tailTrace_3366769 : CollatzResearch.WordTrace tailWord_3366769 prefixEnd_3366769 576256916552414411501339 := by
  unfold tailWord_3366769
  simp only [CollatzResearch.WordTrace]
  refine ⟨122796153539778386212351361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81864102359852257474900907 122796153539778386212351361)
  ·
    refine ⟨92097115154833789659263521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122796153539778386212351361 92097115154833789659263521)
    ·
      refine ⟨69072836366125342244447641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92097115154833789659263521 69072836366125342244447641)
      ·
        refine ⟨51804627274594006683335731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69072836366125342244447641 51804627274594006683335731)
        ·
          refine ⟨77706940911891010025003597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51804627274594006683335731 77706940911891010025003597)
          ·
            refine ⟨29140102841959128759376349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77706940911891010025003597 29140102841959128759376349)
            ·
              refine ⟨10927538565734673284766131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29140102841959128759376349 10927538565734673284766131)
              ·
                refine ⟨16391307848602009927149197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10927538565734673284766131 16391307848602009927149197)
                ·
                  refine ⟨6146740443225753722680949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16391307848602009927149197 6146740443225753722680949)
                  ·
                    refine ⟨576256916552414411501339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6146740443225753722680949 576256916552414411501339)
                    ·
                      rfl

theorem cell23_3366769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_3366769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366769 prefixEnd_3366769 := by exact prefixLift 3366769
  have htrace : WordTrace (prefixWord ++ tailWord_3366769) baseStart_3366769 baseEnd_3366769 := by
    simpa [prefixWord, tailWord_3366769, baseEnd_3366769] using wordTrace_append hprefix tailTrace_3366769
  have hstable : (prefixWord ++ tailWord_3366769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366769).length < 2 ^ (prefixWord ++ tailWord_3366769).sum := by decide
  have hdescent : baseEnd_3366769 < baseStart_3366769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366783 : List Nat := [1, 1, 2, 2, 1, 1, 3, 7, 1, 1, 3]
def baseStart_3366783 : Nat := 118140960795 + 3366783 * 2 ^ 59
def prefixEnd_3366783 : Nat := 4983230072969 + 3 ^ 40 * 3366783 * 2
def baseEnd_3366783 : Nat := 1728777938386406179728953

theorem tailTrace_3366783 : CollatzResearch.WordTrace tailWord_3366783 prefixEnd_3366783 1728777938386406179728953 := by
  unfold tailWord_3366783
  simp only [CollatzResearch.WordTrace]
  refine ⟨122796664161727666603361003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81864442774485111068907335 122796664161727666603361003)
  ·
    refine ⟨184194996242591499905041505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122796664161727666603361003 184194996242591499905041505)
    ·
      refine ⟨138146247181943624928781129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184194996242591499905041505 138146247181943624928781129)
      ·
        refine ⟨103609685386457718696585847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138146247181943624928781129 103609685386457718696585847)
        ·
          refine ⟨155414528079686578044878771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103609685386457718696585847 155414528079686578044878771)
          ·
            refine ⟨233121792119529867067318157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155414528079686578044878771 233121792119529867067318157)
            ·
              refine ⟨87420672044823700150244309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 233121792119529867067318157 87420672044823700150244309)
              ·
                refine ⟨2048922001050555472271351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87420672044823700150244309 2048922001050555472271351)
                ·
                  refine ⟨3073383001575833208407027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048922001050555472271351 3073383001575833208407027)
                  ·
                    refine ⟨4610074502363749812610541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3073383001575833208407027 4610074502363749812610541)
                    ·
                      refine ⟨1728777938386406179728953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4610074502363749812610541 1728777938386406179728953)
                      ·
                        rfl

theorem cell23_3366783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 7, 1, 1, 3].length) (baseStart_3366783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366783 prefixEnd_3366783 := by exact prefixLift 3366783
  have htrace : WordTrace (prefixWord ++ tailWord_3366783) baseStart_3366783 baseEnd_3366783 := by
    simpa [prefixWord, tailWord_3366783, baseEnd_3366783] using wordTrace_append hprefix tailTrace_3366783
  have hstable : (prefixWord ++ tailWord_3366783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366783).length < 2 ^ (prefixWord ++ tailWord_3366783).sum := by decide
  have hdescent : baseEnd_3366783 < baseStart_3366783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366794 : List Nat := [3, 1, 2, 4, 3, 1, 2, 2, 1, 4]
def baseStart_3366794 : Nat := 118140960795 + 3366794 * 2 ^ 59
def prefixEnd_3366794 : Nat := 4983230072969 + 3 ^ 40 * 3366794 * 2
def baseEnd_3366794 : Nat := 576261195557868545563801

theorem tailTrace_3366794 : CollatzResearch.WordTrace tailWord_3366794 prefixEnd_3366794 576261195557868545563801 := by
  unfold tailWord_3366794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30699266341171953870502859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81864710243125210321340957 30699266341171953870502859)
  ·
    refine ⟨46048899511757930805754289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30699266341171953870502859 46048899511757930805754289)
    ·
      refine ⟨34536674633818448104315717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46048899511757930805754289 34536674633818448104315717)
      ·
        refine ⟨6475626493840959019559197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34536674633818448104315717 6475626493840959019559197)
        ·
          refine ⟨2428359935190359632334699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6475626493840959019559197 2428359935190359632334699)
          ·
            refine ⟨3642539902785539448502049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428359935190359632334699 3642539902785539448502049)
            ·
              refine ⟨2731904927089154586376537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642539902785539448502049 2731904927089154586376537)
              ·
                refine ⟨2048928695316865939782403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2731904927089154586376537 2048928695316865939782403)
                ·
                  refine ⟨3073393042975298909673605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2048928695316865939782403 3073393042975298909673605)
                  ·
                    refine ⟨576261195557868545563801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073393042975298909673605 576261195557868545563801)
                    ·
                      rfl

theorem cell23_3366794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_3366794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366794 prefixEnd_3366794 := by exact prefixLift 3366794
  have htrace : WordTrace (prefixWord ++ tailWord_3366794) baseStart_3366794 baseEnd_3366794 := by
    simpa [prefixWord, tailWord_3366794, baseEnd_3366794] using wordTrace_append hprefix tailTrace_3366794
  have hstable : (prefixWord ++ tailWord_3366794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366794).length < 2 ^ (prefixWord ++ tailWord_3366794).sum := by decide
  have hdescent : baseEnd_3366794 < baseStart_3366794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366799 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 10, 4]
def baseStart_3366799 : Nat := 118140960795 + 3366799 * 2 ^ 59
def prefixEnd_3366799 : Nat := 4983230072969 + 3 ^ 40 * 3366799 * 2
def baseEnd_3366799 : Nat := 576262051358959372376293

theorem tailTrace_3366799 : CollatzResearch.WordTrace tailWord_3366799 prefixEnd_3366799 576262051358959372376293 := by
  unfold tailWord_3366799
  simp only [CollatzResearch.WordTrace]
  refine ⟨122797247729669701335943451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81864831819779800890628967 122797247729669701335943451)
  ·
    refine ⟨184195871594504552003915177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122797247729669701335943451 184195871594504552003915177)
    ·
      refine ⟨138146903695878414002936383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184195871594504552003915177 138146903695878414002936383)
      ·
        refine ⟨207220355543817621004404575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138146903695878414002936383 207220355543817621004404575)
        ·
          refine ⟨310830533315726431506606863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207220355543817621004404575 310830533315726431506606863)
          ·
            refine ⟨466245799973589647259910295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310830533315726431506606863 466245799973589647259910295)
            ·
              refine ⟨699368699960384470889865443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466245799973589647259910295 699368699960384470889865443)
              ·
                refine ⟨1049053049940576706334798165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 699368699960384470889865443 1049053049940576706334798165)
                ·
                  refine ⟨3073397607247783319340229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1049053049940576706334798165 3073397607247783319340229)
                  ·
                    refine ⟨576262051358959372376293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073397607247783319340229 576262051358959372376293)
                    ·
                      rfl

theorem cell23_3366799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 10, 4].length) (baseStart_3366799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366799 prefixEnd_3366799 := by exact prefixLift 3366799
  have htrace : WordTrace (prefixWord ++ tailWord_3366799) baseStart_3366799 baseEnd_3366799 := by
    simpa [prefixWord, tailWord_3366799, baseEnd_3366799] using wordTrace_append hprefix tailTrace_3366799
  have hstable : (prefixWord ++ tailWord_3366799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366799).length < 2 ^ (prefixWord ++ tailWord_3366799).sum := by decide
  have hdescent : baseEnd_3366799 < baseStart_3366799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366809 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3366809 : Nat := 118140960795 + 3366809 * 2 ^ 59
def prefixEnd_3366809 : Nat := 4983230072969 + 3 ^ 40 * 3366809 * 2
def baseEnd_3366809 : Nat := 1728791288883423078003833

theorem tailTrace_3366809 : CollatzResearch.WordTrace tailWord_3366809 prefixEnd_3366809 1728791288883423078003833 := by
  unfold tailWord_3366809
  simp only [CollatzResearch.WordTrace]
  refine ⟨122797612459633473043807481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81865074973088982029204987 122797612459633473043807481)
  ·
    refine ⟨92098209344725104782855611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122797612459633473043807481 92098209344725104782855611)
    ·
      refine ⟨138147314017087657174283417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92098209344725104782855611 138147314017087657174283417)
      ·
        refine ⟨103610485512815742880712563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138147314017087657174283417 103610485512815742880712563)
        ·
          refine ⟨155415728269223614321068845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103610485512815742880712563 155415728269223614321068845)
          ·
            refine ⟨58280898100958855370400817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155415728269223614321068845 58280898100958855370400817)
            ·
              refine ⟨43710673575719141527800613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58280898100958855370400817 43710673575719141527800613)
              ·
                refine ⟨8195751295447339036462615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43710673575719141527800613 8195751295447339036462615)
                ·
                  refine ⟨12293626943171008554693923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8195751295447339036462615 12293626943171008554693923)
                  ·
                    refine ⟨18440440414756512832040885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12293626943171008554693923 18440440414756512832040885)
                    ·
                      refine ⟨1728791288883423078003833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18440440414756512832040885 1728791288883423078003833)
                      ·
                        rfl

theorem cell23_3366809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3366809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366809 prefixEnd_3366809 := by exact prefixLift 3366809
  have htrace : WordTrace (prefixWord ++ tailWord_3366809) baseStart_3366809 baseEnd_3366809 := by
    simpa [prefixWord, tailWord_3366809, baseEnd_3366809] using wordTrace_append hprefix tailTrace_3366809
  have hstable : (prefixWord ++ tailWord_3366809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366809).length < 2 ^ (prefixWord ++ tailWord_3366809).sum := by decide
  have hdescent : baseEnd_3366809 < baseStart_3366809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366918 : List Nat := [6, 2, 1, 2, 1, 2, 2, 1, 2, 4]
def baseStart_3366918 : Nat := 118140960795 + 3366918 * 2 ^ 59
def prefixEnd_3366918 : Nat := 4983230072969 + 3 ^ 40 * 3366918 * 2
def baseEnd_3366918 : Nat := 576282419424921050513611

theorem tailTrace_3366918 : CollatzResearch.WordTrace tailWord_3366918 prefixEnd_3366918 576282419424921050513611 := by
  unfold tailWord_3366918
  simp only [CollatzResearch.WordTrace]
  refine ⟨3837549625507455770610169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81867725344159056439683605 3837549625507455770610169)
  ·
    refine ⟨2878162219130591827957627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3837549625507455770610169 2878162219130591827957627)
    ·
      refine ⟨4317243328695887741936441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878162219130591827957627 4317243328695887741936441)
      ·
        refine ⟨3237932496521915806452331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4317243328695887741936441 3237932496521915806452331)
        ·
          refine ⟨4856898744782873709678497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3237932496521915806452331 4856898744782873709678497)
          ·
            refine ⟨3642674058587155282258873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4856898744782873709678497 3642674058587155282258873)
            ·
              refine ⟨2732005543940366461694155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3642674058587155282258873 2732005543940366461694155)
              ·
                refine ⟨4098008315910549692541233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732005543940366461694155 4098008315910549692541233)
                ·
                  refine ⟨3073506236932912269405925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4098008315910549692541233 3073506236932912269405925)
                  ·
                    refine ⟨576282419424921050513611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073506236932912269405925 576282419424921050513611)
                    ·
                      rfl

theorem cell23_3366918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_3366918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366918 prefixEnd_3366918 := by exact prefixLift 3366918
  have htrace : WordTrace (prefixWord ++ tailWord_3366918) baseStart_3366918 baseEnd_3366918 := by
    simpa [prefixWord, tailWord_3366918, baseEnd_3366918] using wordTrace_append hprefix tailTrace_3366918
  have hstable : (prefixWord ++ tailWord_3366918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366918).length < 2 ^ (prefixWord ++ tailWord_3366918).sum := by decide
  have hdescent : baseEnd_3366918 < baseStart_3366918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366926 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4]
def baseStart_3366926 : Nat := 118140960795 + 3366926 * 2 ^ 59
def prefixEnd_3366926 : Nat := 4983230072969 + 3 ^ 40 * 3366926 * 2
def baseEnd_3366926 : Nat := 1728851366119999120240795

theorem tailTrace_3366926 : CollatzResearch.WordTrace tailWord_3366926 prefixEnd_3366926 1728851366119999120240795 := by
  unfold tailWord_3366926
  simp only [CollatzResearch.WordTrace]
  refine ⟨15350234975026200253227079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81867919866806401350544421 15350234975026200253227079)
  ·
    refine ⟨23025352462539300379840619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15350234975026200253227079 23025352462539300379840619)
    ·
      refine ⟨34538028693808950569760929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23025352462539300379840619 34538028693808950569760929)
      ·
        refine ⟨25903521520356712927320697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34538028693808950569760929 25903521520356712927320697)
        ·
          refine ⟨19427641140267534695490523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25903521520356712927320697 19427641140267534695490523)
          ·
            refine ⟨29141461710401302043235785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19427641140267534695490523 29141461710401302043235785)
            ·
              refine ⟨21856096282800976532426839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29141461710401302043235785 21856096282800976532426839)
              ·
                refine ⟨32784144424201464798640259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21856096282800976532426839 32784144424201464798640259)
                ·
                  refine ⟨49176216636302197197960389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32784144424201464798640259 49176216636302197197960389)
                  ·
                    refine ⟨9220540619306661974617573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49176216636302197197960389 9220540619306661974617573)
                    ·
                      refine ⟨1728851366119999120240795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9220540619306661974617573 1728851366119999120240795)
                      ·
                        rfl

theorem cell23_3366926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_3366926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366926 prefixEnd_3366926 := by exact prefixLift 3366926
  have htrace : WordTrace (prefixWord ++ tailWord_3366926) baseStart_3366926 baseEnd_3366926 := by
    simpa [prefixWord, tailWord_3366926, baseEnd_3366926] using wordTrace_append hprefix tailTrace_3366926
  have hstable : (prefixWord ++ tailWord_3366926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366926).length < 2 ^ (prefixWord ++ tailWord_3366926).sum := by decide
  have hdescent : baseEnd_3366926 < baseStart_3366926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366973 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 1, 7, 2]
def baseStart_3366973 : Nat := 118140960795 + 3366973 * 2 ^ 59
def prefixEnd_3366973 : Nat := 4983230072969 + 3 ^ 40 * 3366973 * 2
def baseEnd_3366973 : Nat := 1728875499710760436353079

theorem tailTrace_3366973 : CollatzResearch.WordTrace tailWord_3366973 prefixEnd_3366973 1728875499710760436353079 := by
  unfold tailWord_3366973
  simp only [CollatzResearch.WordTrace]
  refine ⟨122803594031039329052777573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81869062687359552701851715 122803594031039329052777573)
  ·
    refine ⟨23025673880819874197395795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122803594031039329052777573 23025673880819874197395795)
    ·
      refine ⟨34538510821229811296093693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23025673880819874197395795 34538510821229811296093693)
      ·
        refine ⟨12951941557961179236035135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34538510821229811296093693 12951941557961179236035135)
        ·
          refine ⟨19427912336941768854052703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12951941557961179236035135 19427912336941768854052703)
          ·
            refine ⟨29141868505412653281079055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19427912336941768854052703 29141868505412653281079055)
            ·
              refine ⟨43712802758118979921618583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29141868505412653281079055 43712802758118979921618583)
              ·
                refine ⟨65569204137178469882427875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43712802758118979921618583 65569204137178469882427875)
                ·
                  refine ⟨98353806205767704823641813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65569204137178469882427875 98353806205767704823641813)
                  ·
                    refine ⟨2305167332947680581804105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 98353806205767704823641813 2305167332947680581804105)
                    ·
                      refine ⟨1728875499710760436353079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305167332947680581804105 1728875499710760436353079)
                      ·
                        rfl

theorem cell23_3366973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_3366973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366973 prefixEnd_3366973 := by exact prefixLift 3366973
  have htrace : WordTrace (prefixWord ++ tailWord_3366973) baseStart_3366973 baseEnd_3366973 := by
    simpa [prefixWord, tailWord_3366973, baseEnd_3366973] using wordTrace_append hprefix tailTrace_3366973
  have hstable : (prefixWord ++ tailWord_3366973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366973).length < 2 ^ (prefixWord ++ tailWord_3366973).sum := by decide
  have hdescent : baseEnd_3366973 < baseStart_3366973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366976 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_3366976 : Nat := 118140960795 + 3366976 * 2 ^ 59
def prefixEnd_3366976 : Nat := 4983230072969 + 3 ^ 40 * 3366976 * 2
def baseEnd_3366976 : Nat := 1728877040152723924615565

theorem tailTrace_3366976 : CollatzResearch.WordTrace tailWord_3366976 prefixEnd_3366976 1728877040152723924615565 := by
  unfold tailWord_3366976
  simp only [CollatzResearch.WordTrace]
  refine ⟨61401851725014230282568391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81869135633352307043424521 61401851725014230282568391)
  ·
    refine ⟨92102777587521345423852587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61401851725014230282568391 92102777587521345423852587)
    ·
      refine ⟨138154166381282018135778881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92102777587521345423852587 138154166381282018135778881)
      ·
        refine ⟨103615624785961513601834161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138154166381282018135778881 103615624785961513601834161)
        ·
          refine ⟨77711718589471135201375621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103615624785961513601834161 77711718589471135201375621)
          ·
            refine ⟨14570947235525837850257929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77711718589471135201375621 14570947235525837850257929)
            ·
              refine ⟨10928210426644378387693447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14570947235525837850257929 10928210426644378387693447)
              ·
                refine ⟨16392315639966567581540171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10928210426644378387693447 16392315639966567581540171)
                ·
                  refine ⟨24588473459949851372310257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16392315639966567581540171 24588473459949851372310257)
                  ·
                    refine ⟨18441355094962388529232693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24588473459949851372310257 18441355094962388529232693)
                    ·
                      refine ⟨1728877040152723924615565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18441355094962388529232693 1728877040152723924615565)
                      ·
                        rfl

theorem cell23_3366976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_3366976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366976 prefixEnd_3366976 := by exact prefixLift 3366976
  have htrace : WordTrace (prefixWord ++ tailWord_3366976) baseStart_3366976 baseEnd_3366976 := by
    simpa [prefixWord, tailWord_3366976, baseEnd_3366976] using wordTrace_append hprefix tailTrace_3366976
  have hstable : (prefixWord ++ tailWord_3366976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366976).length < 2 ^ (prefixWord ++ tailWord_3366976).sum := by decide
  have hdescent : baseEnd_3366976 < baseStart_3366976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3366986 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_3366986 : Nat := 118140960795 + 3366986 * 2 ^ 59
def prefixEnd_3366986 : Nat := 4983230072969 + 3 ^ 40 * 3366986 * 2
def baseEnd_3366986 : Nat := 1728882174959268885490519

theorem tailTrace_3366986 : CollatzResearch.WordTrace tailWord_3366986 prefixEnd_3366986 1728882174959268885490519 := by
  unfold tailWord_3366986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30701017044998058068250203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81869378786661488182000541 30701017044998058068250203)
  ·
    refine ⟨46051525567497087102375305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30701017044998058068250203 46051525567497087102375305)
    ·
      refine ⟨34538644175622815326781479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46051525567497087102375305 34538644175622815326781479)
      ·
        refine ⟨51807966263434222990172219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34538644175622815326781479 51807966263434222990172219)
        ·
          refine ⟨77711949395151334485258329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51807966263434222990172219 77711949395151334485258329)
          ·
            refine ⟨58283962046363500863943747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77711949395151334485258329 58283962046363500863943747)
            ·
              refine ⟨87425943069545251295915621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58283962046363500863943747 87425943069545251295915621)
              ·
                refine ⟨16392364325539734617984179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87425943069545251295915621 16392364325539734617984179)
                ·
                  refine ⟨24588546488309601926976269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16392364325539734617984179 24588546488309601926976269)
                  ·
                    refine ⟨9220704933116100722616101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24588546488309601926976269 9220704933116100722616101)
                    ·
                      refine ⟨1728882174959268885490519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9220704933116100722616101 1728882174959268885490519)
                      ·
                        rfl

theorem cell23_3366986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_3366986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3366986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3366986 prefixEnd_3366986 := by exact prefixLift 3366986
  have htrace : WordTrace (prefixWord ++ tailWord_3366986) baseStart_3366986 baseEnd_3366986 := by
    simpa [prefixWord, tailWord_3366986, baseEnd_3366986] using wordTrace_append hprefix tailTrace_3366986
  have hstable : (prefixWord ++ tailWord_3366986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3366986).length < 2 ^ (prefixWord ++ tailWord_3366986).sum := by decide
  have hdescent : baseEnd_3366986 < baseStart_3366986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3366986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367030 : List Nat := [5, 1, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_3367030 : Nat := 118140960795 + 3367030 * 2 ^ 59
def prefixEnd_3367030 : Nat := 4983230072969 + 3 ^ 40 * 3367030 * 2
def baseEnd_3367030 : Nat := 576301589369355571113439

theorem tailTrace_3367030 : CollatzResearch.WordTrace tailWord_3367030 prefixEnd_3367030 576301589369355571113439 := by
  unfold tailWord_3367030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7675354561989551736725159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81870448661221885191735029 7675354561989551736725159)
  ·
    refine ⟨11513031842984327605087739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7675354561989551736725159 11513031842984327605087739)
    ·
      refine ⟨17269547764476491407631609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11513031842984327605087739 17269547764476491407631609)
      ·
        refine ⟨12952160823357368555723707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17269547764476491407631609 12952160823357368555723707)
        ·
          refine ⟨19428241235036052833585561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12952160823357368555723707 19428241235036052833585561)
          ·
            refine ⟨14571180926277039625189171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19428241235036052833585561 14571180926277039625189171)
            ·
              refine ⟨21856771389415559437783757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14571180926277039625189171 21856771389415559437783757)
              ·
                refine ⟨8196289271030834789168909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21856771389415559437783757 8196289271030834789168909)
                ·
                  refine ⟨3073608476636563045938341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8196289271030834789168909 3073608476636563045938341)
                  ·
                    refine ⟨576301589369355571113439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073608476636563045938341 576301589369355571113439)
                    ·
                      rfl

theorem cell23_3367030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_3367030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367030 prefixEnd_3367030 := by exact prefixLift 3367030
  have htrace : WordTrace (prefixWord ++ tailWord_3367030) baseStart_3367030 baseEnd_3367030 := by
    simpa [prefixWord, tailWord_3367030, baseEnd_3367030] using wordTrace_append hprefix tailTrace_3367030
  have hstable : (prefixWord ++ tailWord_3367030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367030).length < 2 ^ (prefixWord ++ tailWord_3367030).sum := by decide
  have hdescent : baseEnd_3367030 < baseStart_3367030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367064 : List Nat := [2, 1, 2, 4, 3, 2, 1, 3, 1, 4]
def baseStart_3367064 : Nat := 118140960795 + 3367064 * 2 ^ 59
def prefixEnd_3367064 : Nat := 4983230072969 + 3 ^ 40 * 3367064 * 2
def baseEnd_3367064 : Nat := 576307408816773193438387

theorem tailTrace_3367064 : CollatzResearch.WordTrace tailWord_3367064 prefixEnd_3367064 576307408816773193438387 := by
  unfold tailWord_3367064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61403456536854825797170123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81871275382473101062893497 61403456536854825797170123)
  ·
    refine ⟨92105184805282238695755185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61403456536854825797170123 92105184805282238695755185)
    ·
      refine ⟨69078888603961679021816389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92105184805282238695755185 69078888603961679021816389)
      ·
        refine ⟨12952291613242814816590573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69078888603961679021816389 12952291613242814816590573)
        ·
          refine ⟨4857109354966055556221465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12952291613242814816590573 4857109354966055556221465)
          ·
            refine ⟨3642832016224541667166099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857109354966055556221465 3642832016224541667166099)
            ·
              refine ⟨5464248024336812500749149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3642832016224541667166099 5464248024336812500749149)
              ·
                refine ⟨2049093009126304687780931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5464248024336812500749149 2049093009126304687780931)
                ·
                  refine ⟨3073639513689457031671397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049093009126304687780931 3073639513689457031671397)
                  ·
                    refine ⟨576307408816773193438387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3073639513689457031671397 576307408816773193438387)
                    ·
                      rfl

theorem cell23_3367064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 3, 1, 4].length) (baseStart_3367064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367064 prefixEnd_3367064 := by exact prefixLift 3367064
  have htrace : WordTrace (prefixWord ++ tailWord_3367064) baseStart_3367064 baseEnd_3367064 := by
    simpa [prefixWord, tailWord_3367064, baseEnd_3367064] using wordTrace_append hprefix tailTrace_3367064
  have hstable : (prefixWord ++ tailWord_3367064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367064).length < 2 ^ (prefixWord ++ tailWord_3367064).sum := by decide
  have hdescent : baseEnd_3367064 < baseStart_3367064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367130 : List Nat := [3, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_3367130 : Nat := 118140960795 + 3367130 * 2 ^ 59
def prefixEnd_3367130 : Nat := 4983230072969 + 3 ^ 40 * 3367130 * 2
def baseEnd_3367130 : Nat := 1728956116173516322089857

theorem tailTrace_3367130 : CollatzResearch.WordTrace tailWord_3367130 prefixEnd_3367130 1728956116173516322089857 := by
  unfold tailWord_3367130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30702330072867636216560711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81872880194313696577495229 30702330072867636216560711)
  ·
    refine ⟨46053495109301454324841067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30702330072867636216560711 46053495109301454324841067)
    ·
      refine ⟨69080242663952181487261601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46053495109301454324841067 69080242663952181487261601)
      ·
        refine ⟨51810181997964136115446201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69080242663952181487261601 51810181997964136115446201)
        ·
          refine ⟨38857636498473102086584651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51810181997964136115446201 38857636498473102086584651)
          ·
            refine ⟨58286454747709653129876977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38857636498473102086584651 58286454747709653129876977)
            ·
              refine ⟨43714841060782239847407733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58286454747709653129876977 43714841060782239847407733)
              ·
                refine ⟨4098266349448334985694475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43714841060782239847407733 4098266349448334985694475)
                ·
                  refine ⟨6147399524172502478541713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098266349448334985694475 6147399524172502478541713)
                  ·
                    refine ⟨4610549643129376858906285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6147399524172502478541713 4610549643129376858906285)
                    ·
                      refine ⟨1728956116173516322089857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4610549643129376858906285 1728956116173516322089857)
                      ·
                        rfl

theorem cell23_3367130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_3367130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367130 prefixEnd_3367130 := by exact prefixLift 3367130
  have htrace : WordTrace (prefixWord ++ tailWord_3367130) baseStart_3367130 baseEnd_3367130 := by
    simpa [prefixWord, tailWord_3367130, baseEnd_3367130] using wordTrace_append hprefix tailTrace_3367130
  have hstable : (prefixWord ++ tailWord_3367130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367130).length < 2 ^ (prefixWord ++ tailWord_3367130).sum := by decide
  have hdescent : baseEnd_3367130 < baseStart_3367130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367133 : List Nat := [1, 4, 3, 2, 1, 12]
def baseStart_3367133 : Nat := 118140960795 + 3367133 * 2 ^ 59
def prefixEnd_3367133 : Nat := 4983230072969 + 3 ^ 40 * 3367133 * 2
def baseEnd_3367133 : Nat := 7115052084837365474701

theorem tailTrace_3367133 : CollatzResearch.WordTrace tailWord_3367133 prefixEnd_3367133 7115052084837365474701 := by
  unfold tailWord_3367133
  simp only [CollatzResearch.WordTrace]
  refine ⟨122809429710459676378602053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81872953140306450919068035 122809429710459676378602053)
  ·
    refine ⟨23026768070711189320987885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122809429710459676378602053 23026768070711189320987885)
    ·
      refine ⟨8635038026516695995370457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23026768070711189320987885 8635038026516695995370457)
      ·
        refine ⟨6476278519887521996527843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8635038026516695995370457 6476278519887521996527843)
        ·
          refine ⟨9714417779831282994791765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476278519887521996527843 9714417779831282994791765)
          ·
            refine ⟨7115052084837365474701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9714417779831282994791765 7115052084837365474701)
            ·
              rfl

theorem cell23_3367133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 12].length) (baseStart_3367133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367133 prefixEnd_3367133 := by exact prefixLift 3367133
  have htrace : WordTrace (prefixWord ++ tailWord_3367133) baseStart_3367133 baseEnd_3367133 := by
    simpa [prefixWord, tailWord_3367133, baseEnd_3367133] using wordTrace_append hprefix tailTrace_3367133
  have hstable : (prefixWord ++ tailWord_3367133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367133).length < 2 ^ (prefixWord ++ tailWord_3367133).sum := by decide
  have hdescent : baseEnd_3367133 < baseStart_3367133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367250 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3]
def baseStart_3367250 : Nat := 118140960795 + 3367250 * 2 ^ 59
def prefixEnd_3367250 : Nat := 4983230072969 + 3 ^ 40 * 3367250 * 2
def baseEnd_3367250 : Nat := 1729017733852055852589305

theorem tailTrace_3367250 : CollatzResearch.WordTrace tailWord_3367250 prefixEnd_3367250 1729017733852055852589305 := by
  unfold tailWord_3367250
  simp only [CollatzResearch.WordTrace]
  refine ⟨30703424262758951340152801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81875798034023870240407469 30703424262758951340152801)
  ·
    refine ⟨23027568197069213505114601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30703424262758951340152801 23027568197069213505114601)
    ·
      refine ⟨17270676147801910128835951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23027568197069213505114601 17270676147801910128835951)
      ·
        refine ⟨25906014221702865193253927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17270676147801910128835951 25906014221702865193253927)
        ·
          refine ⟨38859021332554297789880891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25906014221702865193253927 38859021332554297789880891)
          ·
            refine ⟨58288531998831446684821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38859021332554297789880891 58288531998831446684821337)
            ·
              refine ⟨43716398999123585013616003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58288531998831446684821337 43716398999123585013616003)
              ·
                refine ⟨65574598498685377520424005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43716398999123585013616003 65574598498685377520424005)
                ·
                  refine ⟨12295237218503508285079501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65574598498685377520424005 12295237218503508285079501)
                  ·
                    refine ⟨4610713956938815606904813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12295237218503508285079501 4610713956938815606904813)
                    ·
                      refine ⟨1729017733852055852589305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4610713956938815606904813 1729017733852055852589305)
                      ·
                        rfl

theorem cell23_3367250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_3367250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367250 prefixEnd_3367250 := by exact prefixLift 3367250
  have htrace : WordTrace (prefixWord ++ tailWord_3367250) baseStart_3367250 baseEnd_3367250 := by
    simpa [prefixWord, tailWord_3367250, baseEnd_3367250] using wordTrace_append hprefix tailTrace_3367250
  have hstable : (prefixWord ++ tailWord_3367250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367250).length < 2 ^ (prefixWord ++ tailWord_3367250).sum := by decide
  have hdescent : baseEnd_3367250 < baseStart_3367250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367263 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7]
def baseStart_3367263 : Nat := 118140960795 + 3367263 * 2 ^ 59
def prefixEnd_3367263 : Nat := 4983230072969 + 3 ^ 40 * 3367263 * 2
def baseEnd_3367263 : Nat := 1729024409100564301726745

theorem tailTrace_3367263 : CollatzResearch.WordTrace tailWord_3367263 prefixEnd_3367263 1729024409100564301726745 := by
  unfold tailWord_3367263
  simp only [CollatzResearch.WordTrace]
  refine ⟨122814171199988708580834443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81876114133325805720556295 122814171199988708580834443)
  ·
    refine ⟨184221256799983062871251665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122814171199988708580834443 184221256799983062871251665)
    ·
      refine ⟨138165942599987297153438749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184221256799983062871251665 138165942599987297153438749)
      ·
        refine ⟨51812228474995236432539531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138165942599987297153438749 51812228474995236432539531)
        ·
          refine ⟨77718342712492854648809297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51812228474995236432539531 77718342712492854648809297)
          ·
            refine ⟨58288757034369640986606973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77718342712492854648809297 58288757034369640986606973)
            ·
              refine ⟨21858283887888615369977615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58288757034369640986606973 21858283887888615369977615)
              ·
                refine ⟨32787425831832923054966423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21858283887888615369977615 32787425831832923054966423)
                ·
                  refine ⟨49181138747749384582449635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32787425831832923054966423 49181138747749384582449635)
                  ·
                    refine ⟨73771708121624076873674453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49181138747749384582449635 73771708121624076873674453)
                    ·
                      refine ⟨1729024409100564301726745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73771708121624076873674453 1729024409100564301726745)
                      ·
                        rfl

theorem cell23_3367263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_3367263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367263 prefixEnd_3367263 := by exact prefixLift 3367263
  have htrace : WordTrace (prefixWord ++ tailWord_3367263) baseStart_3367263 baseEnd_3367263 := by
    simpa [prefixWord, tailWord_3367263, baseEnd_3367263] using wordTrace_append hprefix tailTrace_3367263
  have hstable : (prefixWord ++ tailWord_3367263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367263).length < 2 ^ (prefixWord ++ tailWord_3367263).sum := by decide
  have hdescent : baseEnd_3367263 < baseStart_3367263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367318 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_3367318 : Nat := 118140960795 + 3367318 * 2 ^ 59
def prefixEnd_3367318 : Nat := 4983230072969 + 3 ^ 40 * 3367318 * 2
def baseEnd_3367318 : Nat := 1729052650536561586538993

theorem tailTrace_3367318 : CollatzResearch.WordTrace tailWord_3367318 prefixEnd_3367318 1729052650536561586538993 := by
  unfold tailWord_3367318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676011075924340810880413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81877451476526301982724405 7676011075924340810880413)
  ·
    refine ⟨2878504153471627804080155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7676011075924340810880413 2878504153471627804080155)
    ·
      refine ⟨4317756230207441706120233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2878504153471627804080155 4317756230207441706120233)
      ·
        refine ⟨3238317172655581279590175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4317756230207441706120233 3238317172655581279590175)
        ·
          refine ⟨4857475758983371919385263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238317172655581279590175 4857475758983371919385263)
          ·
            refine ⟨7286213638475057879077895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857475758983371919385263 7286213638475057879077895)
            ·
              refine ⟨10929320457712586818616843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286213638475057879077895 10929320457712586818616843)
              ·
                refine ⟨16393980686568880227925265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929320457712586818616843 16393980686568880227925265)
                ·
                  refine ⟨12295485514926660170943949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16393980686568880227925265 12295485514926660170943949)
                  ·
                    refine ⟨4610807068097497564103981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12295485514926660170943949 4610807068097497564103981)
                    ·
                      refine ⟨1729052650536561586538993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4610807068097497564103981 1729052650536561586538993)
                      ·
                        rfl

theorem cell23_3367318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_3367318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367318 prefixEnd_3367318 := by exact prefixLift 3367318
  have htrace : WordTrace (prefixWord ++ tailWord_3367318) baseStart_3367318 baseEnd_3367318 := by
    simpa [prefixWord, tailWord_3367318, baseEnd_3367318] using wordTrace_append hprefix tailTrace_3367318
  have hstable : (prefixWord ++ tailWord_3367318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367318).length < 2 ^ (prefixWord ++ tailWord_3367318).sum := by decide
  have hdescent : baseEnd_3367318 < baseStart_3367318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367338 : List Nat := [3, 1, 6, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3367338 : Nat := 118140960795 + 3367338 * 2 ^ 59
def prefixEnd_3367338 : Nat := 4983230072969 + 3 ^ 40 * 3367338 * 2
def baseEnd_3367338 : Nat := 576354306716550502762967

theorem tailTrace_3367338 : CollatzResearch.WordTrace tailWord_3367338 prefixEnd_3367338 576354306716550502762967 := by
  unfold tailWord_3367338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30704226668679249097453667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81877937783144664259876445 30704226668679249097453667)
  ·
    refine ⟨46056340003018873646180501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30704226668679249097453667 46056340003018873646180501)
    ·
      refine ⟨2158890937641509702164711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46056340003018873646180501 2158890937641509702164711)
      ·
        refine ⟨3238336406462264553247067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2158890937641509702164711 3238336406462264553247067)
        ·
          refine ⟨4857504609693396829870601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238336406462264553247067 4857504609693396829870601)
          ·
            refine ⟨3643128457270047622402951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857504609693396829870601 3643128457270047622402951)
            ·
              refine ⟨5464692685905071433604427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643128457270047622402951 5464692685905071433604427)
              ·
                refine ⟨8197039028857607150406641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464692685905071433604427 8197039028857607150406641)
                ·
                  refine ⟨6147779271643205362804981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8197039028857607150406641 6147779271643205362804981)
                  ·
                    refine ⟨576354306716550502762967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6147779271643205362804981 576354306716550502762967)
                    ·
                      rfl

theorem cell23_3367338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3367338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367338 prefixEnd_3367338 := by exact prefixLift 3367338
  have htrace : WordTrace (prefixWord ++ tailWord_3367338) baseStart_3367338 baseEnd_3367338 := by
    simpa [prefixWord, tailWord_3367338, baseEnd_3367338] using wordTrace_append hprefix tailTrace_3367338
  have hstable : (prefixWord ++ tailWord_3367338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367338).length < 2 ^ (prefixWord ++ tailWord_3367338).sum := by decide
  have hdescent : baseEnd_3367338 < baseStart_3367338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367341 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3367341 : Nat := 118140960795 + 3367341 * 2 ^ 59
def prefixEnd_3367341 : Nat := 4983230072969 + 3 ^ 40 * 3367341 * 2
def baseEnd_3367341 : Nat := 1729064460591614996551387

theorem tailTrace_3367341 : CollatzResearch.WordTrace tailWord_3367341 prefixEnd_3367341 1729064460591614996551387 := by
  unfold tailWord_3367341
  simp only [CollatzResearch.WordTrace]
  refine ⟨122817016093706127902173877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81878010729137418601449251 122817016093706127902173877)
  ·
    refine ⟨11514095258784949490828801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122817016093706127902173877 11514095258784949490828801)
    ·
      refine ⟨8635571444088712118121601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11514095258784949490828801 8635571444088712118121601)
      ·
        refine ⟨6476678583066534088591201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8635571444088712118121601 6476678583066534088591201)
        ·
          refine ⟨4857508937299900566443401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6476678583066534088591201 4857508937299900566443401)
          ·
            refine ⟨3643131702974925424832551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857508937299900566443401 3643131702974925424832551)
            ·
              refine ⟨5464697554462388137248827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643131702974925424832551 5464697554462388137248827)
              ·
                refine ⟨8197046331693582205873241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5464697554462388137248827 8197046331693582205873241)
                ·
                  refine ⟨6147784748770186654404931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8197046331693582205873241 6147784748770186654404931)
                  ·
                    refine ⟨9221677123155279981607397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147784748770186654404931 9221677123155279981607397)
                    ·
                      refine ⟨1729064460591614996551387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9221677123155279981607397 1729064460591614996551387)
                      ·
                        rfl

theorem cell23_3367341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3367341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367341 prefixEnd_3367341 := by exact prefixLift 3367341
  have htrace : WordTrace (prefixWord ++ tailWord_3367341) baseStart_3367341 baseEnd_3367341 := by
    simpa [prefixWord, tailWord_3367341, baseEnd_3367341] using wordTrace_append hprefix tailTrace_3367341
  have hstable : (prefixWord ++ tailWord_3367341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367341).length < 2 ^ (prefixWord ++ tailWord_3367341).sum := by decide
  have hdescent : baseEnd_3367341 < baseStart_3367341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367414 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4]
def baseStart_3367414 : Nat := 118140960795 + 3367414 * 2 ^ 59
def prefixEnd_3367414 : Nat := 4983230072969 + 3 ^ 40 * 3367414 * 2
def baseEnd_3367414 : Nat := 1729101944679393210938551

theorem tailTrace_3367414 : CollatzResearch.WordTrace tailWord_3367414 prefixEnd_3367414 1729101944679393210938551 := by
  unfold tailWord_3367414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676229913902603835598831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81879785748294440913054197 7676229913902603835598831)
  ·
    refine ⟨11514344870853905753398247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7676229913902603835598831 11514344870853905753398247)
    ·
      refine ⟨17271517306280858630097371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11514344870853905753398247 17271517306280858630097371)
      ·
        refine ⟨25907275959421287945146057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17271517306280858630097371 25907275959421287945146057)
        ·
          refine ⟨19430456969565965958859543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25907275959421287945146057 19430456969565965958859543)
          ·
            refine ⟨29145685454348948938289315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19430456969565965958859543 29145685454348948938289315)
            ·
              refine ⟨43718528181523423407433973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29145685454348948938289315 43718528181523423407433973)
              ·
                refine ⟨4098612017017820944446935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43718528181523423407433973 4098612017017820944446935)
                ·
                  refine ⟨6147918025526731416670403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098612017017820944446935 6147918025526731416670403)
                  ·
                    refine ⟨9221877038290097125005605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6147918025526731416670403 9221877038290097125005605)
                    ·
                      refine ⟨1729101944679393210938551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9221877038290097125005605 1729101944679393210938551)
                      ·
                        rfl

theorem cell23_3367414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_3367414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367414 prefixEnd_3367414 := by exact prefixLift 3367414
  have htrace : WordTrace (prefixWord ++ tailWord_3367414) baseStart_3367414 baseEnd_3367414 := by
    simpa [prefixWord, tailWord_3367414, baseEnd_3367414] using wordTrace_append hprefix tailTrace_3367414
  have hstable : (prefixWord ++ tailWord_3367414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367414).length < 2 ^ (prefixWord ++ tailWord_3367414).sum := by decide
  have hdescent : baseEnd_3367414 < baseStart_3367414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367444 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_3367444 : Nat := 118140960795 + 3367444 * 2 ^ 59
def prefixEnd_3367444 : Nat := 4983230072969 + 3 ^ 40 * 3367444 * 2
def baseEnd_3367444 : Nat := 1729117349099028093563413

theorem tailTrace_3367444 : CollatzResearch.WordTrace tailWord_3367444 prefixEnd_3367444 1729117349099028093563413 := by
  unfold tailWord_3367444
  simp only [CollatzResearch.WordTrace]
  refine ⟨61410386406166488246586693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81880515208221984328782257 61410386406166488246586693)
  ·
    refine ⟨11514447451156216546235005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61410386406166488246586693 11514447451156216546235005)
    ·
      refine ⟨4317917794183581204838127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11514447451156216546235005 4317917794183581204838127)
      ·
        refine ⟨6476876691275371807257191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4317917794183581204838127 6476876691275371807257191)
        ·
          refine ⟨9715315036913057710885787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476876691275371807257191 9715315036913057710885787)
          ·
            refine ⟨14572972555369586566328681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715315036913057710885787 14572972555369586566328681)
            ·
              refine ⟨10929729416527189924746511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14572972555369586566328681 10929729416527189924746511)
              ·
                refine ⟨16394594124790784887119767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10929729416527189924746511 16394594124790784887119767)
                ·
                  refine ⟨24591891187186177330679651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16394594124790784887119767 24591891187186177330679651)
                  ·
                    refine ⟨36887836780779265996019477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24591891187186177330679651 36887836780779265996019477)
                    ·
                      refine ⟨1729117349099028093563413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36887836780779265996019477 1729117349099028093563413)
                      ·
                        rfl

theorem cell23_3367444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_3367444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367444 prefixEnd_3367444 := by exact prefixLift 3367444
  have htrace : WordTrace (prefixWord ++ tailWord_3367444) baseStart_3367444 baseEnd_3367444 := by
    simpa [prefixWord, tailWord_3367444, baseEnd_3367444] using wordTrace_append hprefix tailTrace_3367444
  have hstable : (prefixWord ++ tailWord_3367444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367444).length < 2 ^ (prefixWord ++ tailWord_3367444).sum := by decide
  have hdescent : baseEnd_3367444 < baseStart_3367444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367464 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_3367464 : Nat := 118140960795 + 3367464 * 2 ^ 59
def prefixEnd_3367464 : Nat := 4983230072969 + 3 ^ 40 * 3367464 * 2
def baseEnd_3367464 : Nat := 1729127618712118015313321

theorem tailTrace_3367464 : CollatzResearch.WordTrace tailWord_3367464 prefixEnd_3367464 1729127618712118015313321 := by
  unfold tailWord_3367464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61410751136130259954450723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81881001514840346605934297 61410751136130259954450723)
  ·
    refine ⟨92116126704195389931676085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61410751136130259954450723 92116126704195389931676085)
    ·
      refine ⟨8635886878518317806094633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92116126704195389931676085 8635886878518317806094633)
      ·
        refine ⟨6476915158888738354570975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8635886878518317806094633 6476915158888738354570975)
        ·
          refine ⟨9715372738333107531856463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6476915158888738354570975 9715372738333107531856463)
          ·
            refine ⟨14573059107499661297784695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715372738333107531856463 14573059107499661297784695)
            ·
              refine ⟨21859588661249491946677043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14573059107499661297784695 21859588661249491946677043)
              ·
                refine ⟨32789382991874237920015565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21859588661249491946677043 32789382991874237920015565)
                ·
                  refine ⟨12296018621952839220005837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32789382991874237920015565 12296018621952839220005837)
                  ·
                    refine ⟨4611006983232314707502189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12296018621952839220005837 4611006983232314707502189)
                    ·
                      refine ⟨1729127618712118015313321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4611006983232314707502189 1729127618712118015313321)
                      ·
                        rfl

theorem cell23_3367464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_3367464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367464 prefixEnd_3367464 := by exact prefixLift 3367464
  have htrace : WordTrace (prefixWord ++ tailWord_3367464) baseStart_3367464 baseEnd_3367464 := by
    simpa [prefixWord, tailWord_3367464, baseEnd_3367464] using wordTrace_append hprefix tailTrace_3367464
  have hstable : (prefixWord ++ tailWord_3367464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367464).length < 2 ^ (prefixWord ++ tailWord_3367464).sum := by decide
  have hdescent : baseEnd_3367464 < baseStart_3367464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367481 : List Nat := [1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 3]
def baseStart_3367481 : Nat := 118140960795 + 3367481 * 2 ^ 59
def prefixEnd_3367481 : Nat := 4983230072969 + 3 ^ 40 * 3367481 * 2
def baseEnd_3367481 : Nat := 1729136347883244448800743

theorem tailTrace_3367481 : CollatzResearch.WordTrace tailWord_3367481 prefixEnd_3367481 1729136347883244448800743 := by
  unfold tailWord_3367481
  simp only [CollatzResearch.WordTrace]
  refine ⟨122822122313198931812270297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81881414875465954541513531 122822122313198931812270297)
  ·
    refine ⟨92116591734899198859202723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122822122313198931812270297 92116591734899198859202723)
    ·
      refine ⟨138174887602348798288804085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92116591734899198859202723 138174887602348798288804085)
      ·
        refine ⟨12953895712720199839575383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138174887602348798288804085 12953895712720199839575383)
        ·
          refine ⟨19430843569080299759363075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12953895712720199839575383 19430843569080299759363075)
          ·
            refine ⟨29146265353620449639044613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19430843569080299759363075 29146265353620449639044613)
            ·
              refine ⟨5464924753803834307320865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29146265353620449639044613 5464924753803834307320865)
              ·
                refine ⟨4098693565352875730490649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5464924753803834307320865 4098693565352875730490649)
                ·
                  refine ⟨3074020174014656797867987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4098693565352875730490649 3074020174014656797867987)
                  ·
                    refine ⟨4611030261021985196801981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3074020174014656797867987 4611030261021985196801981)
                    ·
                      refine ⟨1729136347883244448800743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4611030261021985196801981 1729136347883244448800743)
                      ·
                        rfl

theorem cell23_3367481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_3367481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367481 prefixEnd_3367481 := by exact prefixLift 3367481
  have htrace : WordTrace (prefixWord ++ tailWord_3367481) baseStart_3367481 baseEnd_3367481 := by
    simpa [prefixWord, tailWord_3367481, baseEnd_3367481] using wordTrace_append hprefix tailTrace_3367481
  have hstable : (prefixWord ++ tailWord_3367481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367481).length < 2 ^ (prefixWord ++ tailWord_3367481).sum := by decide
  have hdescent : baseEnd_3367481 < baseStart_3367481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367525 : List Nat := [1, 3, 1, 3, 4, 2, 2, 1, 1, 3, 2]
def baseStart_3367525 : Nat := 118140960795 + 3367525 * 2 ^ 59
def prefixEnd_3367525 : Nat := 4983230072969 + 3 ^ 40 * 3367525 * 2
def baseEnd_3367525 : Nat := 1729158941032042276650541

theorem tailTrace_3367525 : CollatzResearch.WordTrace tailWord_3367525 prefixEnd_3367525 1729158941032042276650541 := by
  unfold tailWord_3367525
  simp only [CollatzResearch.WordTrace]
  refine ⟨122823727125039527326872029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81882484750026351551248019 122823727125039527326872029)
  ·
    refine ⟨46058897671889822747577011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122823727125039527326872029 46058897671889822747577011)
    ·
      refine ⟨69088346507834734121365517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46058897671889822747577011 69088346507834734121365517)
      ·
        refine ⟨25908129940438025295512069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69088346507834734121365517 25908129940438025295512069)
        ·
          refine ⟨4857774363832129742908513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25908129940438025295512069 4857774363832129742908513)
          ·
            refine ⟨3643330772874097307181385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4857774363832129742908513 3643330772874097307181385)
            ·
              refine ⟨2732498079655572980386039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643330772874097307181385 2732498079655572980386039)
              ·
                refine ⟨4098747119483359470579059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732498079655572980386039 4098747119483359470579059)
                ·
                  refine ⟨6148120679225039205868589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098747119483359470579059 6148120679225039205868589)
                  ·
                    refine ⟨2305545254709389702200721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6148120679225039205868589 2305545254709389702200721)
                    ·
                      refine ⟨1729158941032042276650541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305545254709389702200721 1729158941032042276650541)
                      ·
                        rfl

theorem cell23_3367525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_3367525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367525 prefixEnd_3367525 := by exact prefixLift 3367525
  have htrace : WordTrace (prefixWord ++ tailWord_3367525) baseStart_3367525 baseEnd_3367525 := by
    simpa [prefixWord, tailWord_3367525, baseEnd_3367525] using wordTrace_append hprefix tailTrace_3367525
  have hstable : (prefixWord ++ tailWord_3367525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367525).length < 2 ^ (prefixWord ++ tailWord_3367525).sum := by decide
  have hdescent : baseEnd_3367525 < baseStart_3367525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367534 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3367534 : Nat := 118140960795 + 3367534 * 2 ^ 59
def prefixEnd_3367534 : Nat := 4983230072969 + 3 ^ 40 * 3367534 * 2
def baseEnd_3367534 : Nat := 1729163562357932741437999

theorem tailTrace_3367534 : CollatzResearch.WordTrace tailWord_3367534 prefixEnd_3367534 1729163562357932741437999 := by
  unfold tailWord_3367534
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353006922750865232993707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81882703588004614575966437 15353006922750865232993707)
  ·
    refine ⟨23029510384126297849490561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15353006922750865232993707 23029510384126297849490561)
    ·
      refine ⟨17272132788094723387117921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23029510384126297849490561 17272132788094723387117921)
      ·
        refine ⟨12954099591071042540338441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17272132788094723387117921 12954099591071042540338441)
        ·
          refine ⟨9715574693303281905253831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12954099591071042540338441 9715574693303281905253831)
          ·
            refine ⟨14573362039954922857880747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715574693303281905253831 14573362039954922857880747)
            ·
              refine ⟨21860043059932384286821121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14573362039954922857880747 21860043059932384286821121)
              ·
                refine ⟨16395032294949288215115841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21860043059932384286821121 16395032294949288215115841)
                ·
                  refine ⟨12296274221211966161336881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16395032294949288215115841 12296274221211966161336881)
                  ·
                    refine ⟨9222205665908974621002661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12296274221211966161336881 9222205665908974621002661)
                    ·
                      refine ⟨1729163562357932741437999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9222205665908974621002661 1729163562357932741437999)
                      ·
                        rfl

theorem cell23_3367534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3367534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367534 prefixEnd_3367534 := by exact prefixLift 3367534
  have htrace : WordTrace (prefixWord ++ tailWord_3367534) baseStart_3367534 baseEnd_3367534 := by
    simpa [prefixWord, tailWord_3367534, baseEnd_3367534] using wordTrace_append hprefix tailTrace_3367534
  have hstable : (prefixWord ++ tailWord_3367534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367534).length < 2 ^ (prefixWord ++ tailWord_3367534).sum := by decide
  have hdescent : baseEnd_3367534 < baseStart_3367534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367538 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 4, 2, 2]
def baseStart_3367538 : Nat := 118140960795 + 3367538 * 2 ^ 59
def prefixEnd_3367538 : Nat := 4983230072969 + 3 ^ 40 * 3367538 * 2
def baseEnd_3367538 : Nat := 1729165616280550725787981

theorem tailTrace_3367538 : CollatzResearch.WordTrace tailWord_3367538 prefixEnd_3367538 1729165616280550725787981 := by
  unfold tailWord_3367538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30706050318498107636773817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81882800849328287031396845 30706050318498107636773817)
  ·
    refine ⟨23029537738873580727580363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30706050318498107636773817 23029537738873580727580363)
    ·
      refine ⟨34544306608310371091370545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23029537738873580727580363 34544306608310371091370545)
      ·
        refine ⟨25908229956232778318527909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34544306608310371091370545 25908229956232778318527909)
        ·
          refine ⟨4857793116793645934723983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25908229956232778318527909 4857793116793645934723983)
          ·
            refine ⟨7286689675190468902085975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857793116793645934723983 7286689675190468902085975)
            ·
              refine ⟨10930034512785703353128963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286689675190468902085975 10930034512785703353128963)
              ·
                refine ⟨16395051769178555029693445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10930034512785703353128963 16395051769178555029693445)
                ·
                  refine ⟨3074072206720979068067521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16395051769178555029693445 3074072206720979068067521)
                  ·
                    refine ⟨2305554155040734301050641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3074072206720979068067521 2305554155040734301050641)
                    ·
                      refine ⟨1729165616280550725787981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305554155040734301050641 1729165616280550725787981)
                      ·
                        rfl

theorem cell23_3367538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_3367538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367538 prefixEnd_3367538 := by exact prefixLift 3367538
  have htrace : WordTrace (prefixWord ++ tailWord_3367538) baseStart_3367538 baseEnd_3367538 := by
    simpa [prefixWord, tailWord_3367538, baseEnd_3367538] using wordTrace_append hprefix tailTrace_3367538
  have hstable : (prefixWord ++ tailWord_3367538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367538).length < 2 ^ (prefixWord ++ tailWord_3367538).sum := by decide
  have hdescent : baseEnd_3367538 < baseStart_3367538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367557 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_3367557 : Nat := 118140960795 + 3367557 * 2 ^ 59
def prefixEnd_3367557 : Nat := 4983230072969 + 3 ^ 40 * 3367557 * 2
def baseEnd_3367557 : Nat := 576391790804328717150131

theorem tailTrace_3367557 : CollatzResearch.WordTrace tailWord_3367557 prefixEnd_3367557 576391790804328717150131 := by
  unfold tailWord_3367557
  simp only [CollatzResearch.WordTrace]
  refine ⟨122824894260923596792036925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81883262840615731194691283 122824894260923596792036925)
  ·
    refine ⟨46059335347846348797013847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122824894260923596792036925 46059335347846348797013847)
    ·
      refine ⟨69089003021769523195520771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46059335347846348797013847 69089003021769523195520771)
      ·
        refine ⟨103633504532654284793281157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69089003021769523195520771 103633504532654284793281157)
        ·
          refine ⟨19431282099872678398740217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103633504532654284793281157 19431282099872678398740217)
          ·
            refine ⟨14573461574904508799055163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19431282099872678398740217 14573461574904508799055163)
            ·
              refine ⟨21860192362356763198582745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14573461574904508799055163 21860192362356763198582745)
              ·
                refine ⟨16395144271767572398937059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21860192362356763198582745 16395144271767572398937059)
                ·
                  refine ⟨24592716407651358598405589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16395144271767572398937059 24592716407651358598405589)
                  ·
                    refine ⟨576391790804328717150131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24592716407651358598405589 576391790804328717150131)
                    ·
                      rfl

theorem cell23_3367557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_3367557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367557 prefixEnd_3367557 := by exact prefixLift 3367557
  have htrace : WordTrace (prefixWord ++ tailWord_3367557) baseStart_3367557 baseEnd_3367557 := by
    simpa [prefixWord, tailWord_3367557, baseEnd_3367557] using wordTrace_append hprefix tailTrace_3367557
  have hstable : (prefixWord ++ tailWord_3367557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367557).length < 2 ^ (prefixWord ++ tailWord_3367557).sum := by decide
  have hdescent : baseEnd_3367557 < baseStart_3367557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367577 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 4]
def baseStart_3367577 : Nat := 118140960795 + 3367577 * 2 ^ 59
def prefixEnd_3367577 : Nat := 4983230072969 + 3 ^ 40 * 3367577 * 2
def baseEnd_3367577 : Nat := 1729185642026076073200301

theorem tailTrace_3367577 : CollatzResearch.WordTrace tailWord_3367577 prefixEnd_3367577 1729185642026076073200301 := by
  unfold tailWord_3367577
  simp only [CollatzResearch.WordTrace]
  refine ⟨122825623720851140207764985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81883749147234093471843323 122825623720851140207764985)
  ·
    refine ⟨92119217790638355155823739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122825623720851140207764985 92119217790638355155823739)
    ·
      refine ⟨138178826685957532733735609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92119217790638355155823739 138178826685957532733735609)
      ·
        refine ⟨103634120014468149550301707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138178826685957532733735609 103634120014468149550301707)
        ·
          refine ⟨155451180021702224325452561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103634120014468149550301707 155451180021702224325452561)
          ·
            refine ⟨116588385016276668244089421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155451180021702224325452561 116588385016276668244089421)
            ·
              refine ⟨43720644381103750591533533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116588385016276668244089421 43720644381103750591533533)
              ·
                refine ⟨16395241642913906471825075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43720644381103750591533533 16395241642913906471825075)
                ·
                  refine ⟨24592862464370859707737613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16395241642913906471825075 24592862464370859707737613)
                  ·
                    refine ⟨9222323424139072390401605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24592862464370859707737613 9222323424139072390401605)
                    ·
                      refine ⟨1729185642026076073200301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9222323424139072390401605 1729185642026076073200301)
                      ·
                        rfl

theorem cell23_3367577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_3367577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367577 prefixEnd_3367577 := by exact prefixLift 3367577
  have htrace : WordTrace (prefixWord ++ tailWord_3367577) baseStart_3367577 baseEnd_3367577 := by
    simpa [prefixWord, tailWord_3367577, baseEnd_3367577] using wordTrace_append hprefix tailTrace_3367577
  have hstable : (prefixWord ++ tailWord_3367577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367577).length < 2 ^ (prefixWord ++ tailWord_3367577).sum := by decide
  have hdescent : baseEnd_3367577 < baseStart_3367577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367601 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 5]
def baseStart_3367601 : Nat := 118140960795 + 3367601 * 2 ^ 59
def prefixEnd_3367601 : Nat := 4983230072969 + 3 ^ 40 * 3367601 * 2
def baseEnd_3367601 : Nat := 1729197965561783979300191

theorem tailTrace_3367601 : CollatzResearch.WordTrace tailWord_3367601 prefixEnd_3367601 1729197965561783979300191 := by
  unfold tailWord_3367601
  simp only [CollatzResearch.WordTrace]
  refine ⟨122826499072764192306638657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81884332715176128204425771 122826499072764192306638657)
  ·
    refine ⟨92119874304573144229978993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122826499072764192306638657 92119874304573144229978993)
    ·
      refine ⟨69089905728429858172484245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92119874304573144229978993 69089905728429858172484245)
      ·
        refine ⟨3238589331020149601835199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69089905728429858172484245 3238589331020149601835199)
        ·
          refine ⟨4857883996530224402752799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238589331020149601835199 4857883996530224402752799)
          ·
            refine ⟨7286825994795336604129199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4857883996530224402752799 7286825994795336604129199)
            ·
              refine ⟨10930238992193004906193799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7286825994795336604129199 10930238992193004906193799)
              ·
                refine ⟨16395358488289507359290699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10930238992193004906193799 16395358488289507359290699)
                ·
                  refine ⟨24593037732434261038936049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16395358488289507359290699 24593037732434261038936049)
                  ·
                    refine ⟨18444778299325695779202037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24593037732434261038936049 18444778299325695779202037)
                    ·
                      refine ⟨1729197965561783979300191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18444778299325695779202037 1729197965561783979300191)
                      ·
                        rfl

theorem cell23_3367601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_3367601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367601 prefixEnd_3367601 := by exact prefixLift 3367601
  have htrace : WordTrace (prefixWord ++ tailWord_3367601) baseStart_3367601 baseEnd_3367601 := by
    simpa [prefixWord, tailWord_3367601, baseEnd_3367601] using wordTrace_append hprefix tailTrace_3367601
  have hstable : (prefixWord ++ tailWord_3367601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367601).length < 2 ^ (prefixWord ++ tailWord_3367601).sum := by decide
  have hdescent : baseEnd_3367601 < baseStart_3367601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367606 : List Nat := [5, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2]
def baseStart_3367606 : Nat := 118140960795 + 3367606 * 2 ^ 59
def prefixEnd_3367606 : Nat := 4983230072969 + 3 ^ 40 * 3367606 * 2
def baseEnd_3367606 : Nat := 1729200532965056459737669

theorem tailTrace_3367606 : CollatzResearch.WordTrace tailWord_3367606 prefixEnd_3367606 1729200532965056459737669 := by
  unfold tailWord_3367606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7676667589859129885035667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81884454291830718773713781 7676667589859129885035667)
  ·
    refine ⟨11515001384788694827553501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7676667589859129885035667 11515001384788694827553501)
    ·
      refine ⟨4318125519295760560332563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11515001384788694827553501 4318125519295760560332563)
      ·
        refine ⟨6477188278943640840498845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4318125519295760560332563 6477188278943640840498845)
        ·
          refine ⟨2428945604603865315187067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6477188278943640840498845 2428945604603865315187067)
          ·
            refine ⟨3643418406905797972780601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2428945604603865315187067 3643418406905797972780601)
            ·
              refine ⟨2732563805179348479585451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3643418406905797972780601 2732563805179348479585451)
              ·
                refine ⟨4098845707769022719378177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732563805179348479585451 4098845707769022719378177)
                ·
                  refine ⟨3074134280826767039533633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4098845707769022719378177 3074134280826767039533633)
                  ·
                    refine ⟨2305600710620075279650225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3074134280826767039533633 2305600710620075279650225)
                    ·
                      refine ⟨1729200532965056459737669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305600710620075279650225 1729200532965056459737669)
                      ·
                        rfl

theorem cell23_3367606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_3367606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367606 prefixEnd_3367606 := by exact prefixLift 3367606
  have htrace : WordTrace (prefixWord ++ tailWord_3367606) baseStart_3367606 baseEnd_3367606 := by
    simpa [prefixWord, tailWord_3367606, baseEnd_3367606] using wordTrace_append hprefix tailTrace_3367606
  have hstable : (prefixWord ++ tailWord_3367606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367606).length < 2 ^ (prefixWord ++ tailWord_3367606).sum := by decide
  have hdescent : baseEnd_3367606 < baseStart_3367606 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367651 : List Nat := [1, 1, 1, 7, 1, 2, 2, 2, 6]
def baseStart_3367651 : Nat := 118140960795 + 3367651 * 2 ^ 59
def prefixEnd_3367651 : Nat := 4983230072969 + 3 ^ 40 * 3367651 * 2
def baseEnd_3367651 : Nat := 192135959954945420408329

theorem tailTrace_3367651 : CollatzResearch.WordTrace tailWord_3367651 prefixEnd_3367651 192135959954945420408329 := by
  unfold tailWord_3367651
  simp only [CollatzResearch.WordTrace]
  refine ⟨122828322722583050845958807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81885548481722033897305871 122828322722583050845958807)
  ·
    refine ⟨184242484083874576268938211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122828322722583050845958807 184242484083874576268938211)
    ·
      refine ⟨276363726125811864403407317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184242484083874576268938211 276363726125811864403407317)
      ·
        refine ⟨6477274831073715571954859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 276363726125811864403407317 6477274831073715571954859)
        ·
          refine ⟨9715912246610573357932289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6477274831073715571954859 9715912246610573357932289)
          ·
            refine ⟨7286934184957930018449217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9715912246610573357932289 7286934184957930018449217)
            ·
              refine ⟨5465200638718447513836913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7286934184957930018449217 5465200638718447513836913)
              ·
                refine ⟨4098900479038835635377685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5465200638718447513836913 4098900479038835635377685)
                ·
                  refine ⟨192135959954945420408329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4098900479038835635377685 192135959954945420408329)
                  ·
                    rfl

theorem cell23_3367651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 2, 6].length) (baseStart_3367651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367651 prefixEnd_3367651 := by exact prefixLift 3367651
  have htrace : WordTrace (prefixWord ++ tailWord_3367651) baseStart_3367651 baseEnd_3367651 := by
    simpa [prefixWord, tailWord_3367651, baseEnd_3367651] using wordTrace_append hprefix tailTrace_3367651
  have hstable : (prefixWord ++ tailWord_3367651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367651).length < 2 ^ (prefixWord ++ tailWord_3367651).sum := by decide
  have hdescent : baseEnd_3367651 < baseStart_3367651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367678 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 5, 1, 3]
def baseStart_3367678 : Nat := 118140960795 + 3367678 * 2 ^ 59
def prefixEnd_3367678 : Nat := 4983230072969 + 3 ^ 40 * 3367678 * 2
def baseEnd_3367678 : Nat := 1729237503572180178037337

theorem tailTrace_3367678 : CollatzResearch.WordTrace tailWord_3367678 prefixEnd_3367678 1729237503572180178037337 := by
  unfold tailWord_3367678
  simp only [CollatzResearch.WordTrace]
  refine ⟨15353663436685654307148961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81886204995656822971461125 15353663436685654307148961)
  ·
    refine ⟨11515247577514240730361721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15353663436685654307148961 11515247577514240730361721)
    ·
      refine ⟨8636435683135680547771291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11515247577514240730361721 8636435683135680547771291)
      ·
        refine ⟨12954653524703520821656937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8636435683135680547771291 12954653524703520821656937)
        ·
          refine ⟨9715990143527640616242703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12954653524703520821656937 9715990143527640616242703)
          ·
            refine ⟨14573985215291460924364055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9715990143527640616242703 14573985215291460924364055)
            ·
              refine ⟨21860977822937191386546083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14573985215291460924364055 21860977822937191386546083)
              ·
                refine ⟨32791466734405787079819125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21860977822937191386546083 32791466734405787079819125)
                ·
                  refine ⟨3074200006350542538733043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32791466734405787079819125 3074200006350542538733043)
                  ·
                    refine ⟨4611300009525813808099565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3074200006350542538733043 4611300009525813808099565)
                    ·
                      refine ⟨1729237503572180178037337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4611300009525813808099565 1729237503572180178037337)
                      ·
                        rfl

theorem cell23_3367678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_3367678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367678 prefixEnd_3367678 := by exact prefixLift 3367678
  have htrace : WordTrace (prefixWord ++ tailWord_3367678) baseStart_3367678 baseEnd_3367678 := by
    simpa [prefixWord, tailWord_3367678, baseEnd_3367678] using wordTrace_append hprefix tailTrace_3367678
  have hstable : (prefixWord ++ tailWord_3367678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367678).length < 2 ^ (prefixWord ++ tailWord_3367678).sum := by decide
  have hdescent : baseEnd_3367678 < baseStart_3367678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367688 : List Nat := [2, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2]
def baseStart_3367688 : Nat := 118140960795 + 3367688 * 2 ^ 59
def prefixEnd_3367688 : Nat := 4983230072969 + 3 ^ 40 * 3367688 * 2
def baseEnd_3367688 : Nat := 1729242638378725138912291

theorem tailTrace_3367688 : CollatzResearch.WordTrace tailWord_3367688 prefixEnd_3367688 1729242638378725138912291 := by
  unfold tailWord_3367688
  simp only [CollatzResearch.WordTrace]
  refine ⟨61414836111724503082527859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81886448148966004110037145 61414836111724503082527859)
  ·
    refine ⟨92122254167586754623791789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61414836111724503082527859 92122254167586754623791789)
    ·
      refine ⟨34545845312845032983921921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92122254167586754623791789 34545845312845032983921921)
      ·
        refine ⟨25909383984633774737941441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34545845312845032983921921 25909383984633774737941441)
        ·
          refine ⟨19432037988475331053456081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25909383984633774737941441 19432037988475331053456081)
          ·
            refine ⟨14574028491356498290092061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19432037988475331053456081 14574028491356498290092061)
            ·
              refine ⟨5465260684258686858784523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14574028491356498290092061 5465260684258686858784523)
              ·
                refine ⟨8197891026388030288176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465260684258686858784523 8197891026388030288176785)
                ·
                  refine ⟨6148418269791022716132589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8197891026388030288176785 6148418269791022716132589)
                  ·
                    refine ⟨2305656851171633518549721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6148418269791022716132589 2305656851171633518549721)
                    ·
                      refine ⟨1729242638378725138912291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305656851171633518549721 1729242638378725138912291)
                      ·
                        rfl

theorem cell23_3367688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_3367688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367688 prefixEnd_3367688 := by exact prefixLift 3367688
  have htrace : WordTrace (prefixWord ++ tailWord_3367688) baseStart_3367688 baseEnd_3367688 := by
    simpa [prefixWord, tailWord_3367688, baseEnd_3367688] using wordTrace_append hprefix tailTrace_3367688
  have hstable : (prefixWord ++ tailWord_3367688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367688).length < 2 ^ (prefixWord ++ tailWord_3367688).sum := by decide
  have hdescent : baseEnd_3367688 < baseStart_3367688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367701 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 4]
def baseStart_3367701 : Nat := 118140960795 + 3367701 * 2 ^ 59
def prefixEnd_3367701 : Nat := 4983230072969 + 3 ^ 40 * 3367701 * 2
def baseEnd_3367701 : Nat := 1729249313627233588049731

theorem tailTrace_3367701 : CollatzResearch.WordTrace tailWord_3367701 prefixEnd_3367701 1729249313627233588049731 := by
  unfold tailWord_3367701
  simp only [CollatzResearch.WordTrace]
  refine ⟨122830146372401909385278957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81886764248267939590185971 122830146372401909385278957)
  ·
    refine ⟨46061304889650716019479609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122830146372401909385278957 46061304889650716019479609)
    ·
      refine ⟨34545978667238037014609707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46061304889650716019479609 34545978667238037014609707)
      ·
        refine ⟨51818968000857055521914561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34545978667238037014609707 51818968000857055521914561)
        ·
          refine ⟨38864226000642791641435921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51818968000857055521914561 38864226000642791641435921)
          ·
            refine ⟨29148169500482093731076941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38864226000642791641435921 29148169500482093731076941)
            ·
              refine ⟨10930563562680785149153853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29148169500482093731076941 10930563562680785149153853)
              ·
                refine ⟨4098961336005294430932695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10930563562680785149153853 4098961336005294430932695)
                ·
                  refine ⟨6148442004007941646399043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4098961336005294430932695 6148442004007941646399043)
                  ·
                    refine ⟨9222663006011912469598565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6148442004007941646399043 9222663006011912469598565)
                    ·
                      refine ⟨1729249313627233588049731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9222663006011912469598565 1729249313627233588049731)
                      ·
                        rfl

theorem cell23_3367701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 1, 1, 4].length) (baseStart_3367701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367701 prefixEnd_3367701 := by exact prefixLift 3367701
  have htrace : WordTrace (prefixWord ++ tailWord_3367701) baseStart_3367701 baseEnd_3367701 := by
    simpa [prefixWord, tailWord_3367701, baseEnd_3367701] using wordTrace_append hprefix tailTrace_3367701
  have hstable : (prefixWord ++ tailWord_3367701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367701).length < 2 ^ (prefixWord ++ tailWord_3367701).sum := by decide
  have hdescent : baseEnd_3367701 < baseStart_3367701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367704 : List Nat := [2, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3367704 : Nat := 118140960795 + 3367704 * 2 ^ 59
def prefixEnd_3367704 : Nat := 4983230072969 + 3 ^ 40 * 3367704 * 2
def baseEnd_3367704 : Nat := 1729250854069197076312217

theorem tailTrace_3367704 : CollatzResearch.WordTrace tailWord_3367704 prefixEnd_3367704 1729250854069197076312217 := by
  unfold tailWord_3367704
  simp only [CollatzResearch.WordTrace]
  refine ⟨61415127895695520448819083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81886837194260693931758777 61415127895695520448819083)
  ·
    refine ⟨92122691843543280673228625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61415127895695520448819083 92122691843543280673228625)
    ·
      refine ⟨69092018882657460504921469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92122691843543280673228625 69092018882657460504921469)
      ·
        refine ⟨25909507080996547689345551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69092018882657460504921469 25909507080996547689345551)
        ·
          refine ⟨38864260621494821534018327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25909507080996547689345551 38864260621494821534018327)
          ·
            refine ⟨58296390932242232301027491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38864260621494821534018327 58296390932242232301027491)
            ·
              refine ⟨87444586398363348451541237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58296390932242232301027491 87444586398363348451541237)
              ·
                refine ⟨8197929974846563917331991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87444586398363348451541237 8197929974846563917331991)
                ·
                  refine ⟨12296894962269845875997987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8197929974846563917331991 12296894962269845875997987)
                  ·
                    refine ⟨18445342443404768813996981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12296894962269845875997987 18445342443404768813996981)
                    ·
                      refine ⟨1729250854069197076312217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18445342443404768813996981 1729250854069197076312217)
                      ·
                        rfl

theorem cell23_3367704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3367704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367704 prefixEnd_3367704 := by exact prefixLift 3367704
  have htrace : WordTrace (prefixWord ++ tailWord_3367704) baseStart_3367704 baseEnd_3367704 := by
    simpa [prefixWord, tailWord_3367704, baseEnd_3367704] using wordTrace_append hprefix tailTrace_3367704
  have hstable : (prefixWord ++ tailWord_3367704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367704).length < 2 ^ (prefixWord ++ tailWord_3367704).sum := by decide
  have hdescent : baseEnd_3367704 < baseStart_3367704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367711 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 4, 4]
def baseStart_3367711 : Nat := 118140960795 + 3367711 * 2 ^ 59
def prefixEnd_3367711 : Nat := 4983230072969 + 3 ^ 40 * 3367711 * 2
def baseEnd_3367711 : Nat := 576418149477926182974895

theorem tailTrace_3367711 : CollatzResearch.WordTrace tailWord_3367711 prefixEnd_3367711 576418149477926182974895 := by
  unfold tailWord_3367711
  simp only [CollatzResearch.WordTrace]
  refine ⟨122830511102365681093142987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81887007401577120728761991 122830511102365681093142987)
  ·
    refine ⟨184245766653548521639714481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122830511102365681093142987 184245766653548521639714481)
    ·
      refine ⟨138184324990161391229785861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184245766653548521639714481 138184324990161391229785861)
      ·
        refine ⟨25909560935655260855584849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138184324990161391229785861 25909560935655260855584849)
        ·
          refine ⟨19432170701741445641688637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25909560935655260855584849 19432170701741445641688637)
          ·
            refine ⟨7287064013153042115633239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19432170701741445641688637 7287064013153042115633239)
            ·
              refine ⟨10930596019729563173449859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7287064013153042115633239 10930596019729563173449859)
              ·
                refine ⟨16395894029594344760174789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10930596019729563173449859 16395894029594344760174789)
                ·
                  refine ⟨3074230130548939642532773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16395894029594344760174789 3074230130548939642532773)
                  ·
                    refine ⟨576418149477926182974895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074230130548939642532773 576418149477926182974895)
                    ·
                      rfl

theorem cell23_3367711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 4, 4].length) (baseStart_3367711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367711 prefixEnd_3367711 := by exact prefixLift 3367711
  have htrace : WordTrace (prefixWord ++ tailWord_3367711) baseStart_3367711 baseEnd_3367711 := by
    simpa [prefixWord, tailWord_3367711, baseEnd_3367711] using wordTrace_append hprefix tailTrace_3367711
  have hstable : (prefixWord ++ tailWord_3367711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367711).length < 2 ^ (prefixWord ++ tailWord_3367711).sum := by decide
  have hdescent : baseEnd_3367711 < baseStart_3367711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367731 : List Nat := [1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4]
def baseStart_3367731 : Nat := 118140960795 + 3367731 * 2 ^ 59
def prefixEnd_3367731 : Nat := 4983230072969 + 3 ^ 40 * 3367731 * 2
def baseEnd_3367731 : Nat := 1729264718046868470674593

theorem tailTrace_3367731 : CollatzResearch.WordTrace tailWord_3367731 prefixEnd_3367731 1729264718046868470674593 := by
  unfold tailWord_3367731
  simp only [CollatzResearch.WordTrace]
  refine ⟨122831240562293224508871047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81887493708195483005914031 122831240562293224508871047)
  ·
    refine ⟨184246860843439836763306571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122831240562293224508871047 184246860843439836763306571)
    ·
      refine ⟨276370291265159755144959857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184246860843439836763306571 276370291265159755144959857)
      ·
        refine ⟨207277718448869816358719893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276370291265159755144959857 207277718448869816358719893)
        ·
          refine ⟨9716143052290772641814995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 207277718448869816358719893 9716143052290772641814995)
          ·
            refine ⟨14574214578436158962722493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716143052290772641814995 14574214578436158962722493)
            ·
              refine ⟨5465330466913559611020935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14574214578436158962722493 5465330466913559611020935)
              ·
                refine ⟨8197995700370339416531403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5465330466913559611020935 8197995700370339416531403)
                ·
                  refine ⟨12296993550555509124797105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8197995700370339416531403 12296993550555509124797105)
                  ·
                    refine ⟨9222745162916631843597829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12296993550555509124797105 9222745162916631843597829)
                    ·
                      refine ⟨1729264718046868470674593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9222745162916631843597829 1729264718046868470674593)
                      ·
                        rfl

theorem cell23_3367731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_3367731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367731 prefixEnd_3367731 := by exact prefixLift 3367731
  have htrace : WordTrace (prefixWord ++ tailWord_3367731) baseStart_3367731 baseEnd_3367731 := by
    simpa [prefixWord, tailWord_3367731, baseEnd_3367731] using wordTrace_append hprefix tailTrace_3367731
  have hstable : (prefixWord ++ tailWord_3367731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367731).length < 2 ^ (prefixWord ++ tailWord_3367731).sum := by decide
  have hdescent : baseEnd_3367731 < baseStart_3367731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367741 : List Nat := [1, 4, 1, 4, 2, 1, 1, 9]
def baseStart_3367741 : Nat := 118140960795 + 3367741 * 2 ^ 59
def prefixEnd_3367741 : Nat := 4983230072969 + 3 ^ 40 * 3367741 * 2
def baseEnd_3367741 : Nat := 64047031587163460427761

theorem tailTrace_3367741 : CollatzResearch.WordTrace tailWord_3367741 prefixEnd_3367741 64047031587163460427761 := by
  unfold tailWord_3367741
  simp only [CollatzResearch.WordTrace]
  refine ⟨122831605292256996216735077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81887736861504664144490051 122831605292256996216735077)
  ·
    refine ⟨23030925992298186790637827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122831605292256996216735077 23030925992298186790637827)
    ·
      refine ⟨34546388988447280185956741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23030925992298186790637827 34546388988447280185956741)
      ·
        refine ⟨6477447935333865034866889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34546388988447280185956741 6477447935333865034866889)
        ·
          refine ⟨4858085951500398776150167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6477447935333865034866889 4858085951500398776150167)
          ·
            refine ⟨7287128927250598164225251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858085951500398776150167 7287128927250598164225251)
            ·
              refine ⟨10930693390875897246337877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7287128927250598164225251 10930693390875897246337877)
              ·
                refine ⟨64047031587163460427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10930693390875897246337877 64047031587163460427761)
                ·
                  rfl

theorem cell23_3367741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 1, 9].length) (baseStart_3367741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367741 prefixEnd_3367741 := by exact prefixLift 3367741
  have htrace : WordTrace (prefixWord ++ tailWord_3367741) baseStart_3367741 baseEnd_3367741 := by
    simpa [prefixWord, tailWord_3367741, baseEnd_3367741] using wordTrace_append hprefix tailTrace_3367741
  have hstable : (prefixWord ++ tailWord_3367741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367741).length < 2 ^ (prefixWord ++ tailWord_3367741).sum := by decide
  have hdescent : baseEnd_3367741 < baseStart_3367741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367791 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 5, 4, 2]
def baseStart_3367791 : Nat := 118140960795 + 3367791 * 2 ^ 59
def prefixEnd_3367791 : Nat := 4983230072969 + 3 ^ 40 * 3367791 * 2
def baseEnd_3367791 : Nat := 1729295526886138235924317

theorem tailTrace_3367791 : CollatzResearch.WordTrace tailWord_3367791 prefixEnd_3367791 1729295526886138235924317 := by
  unfold tailWord_3367791
  simp only [CollatzResearch.WordTrace]
  refine ⟨122833428942075854756055227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81888952628050569837370151 122833428942075854756055227)
  ·
    refine ⟨184250143413113782134082841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122833428942075854756055227 184250143413113782134082841)
    ·
      refine ⟨138187607559835336600562131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184250143413113782134082841 138187607559835336600562131)
      ·
        refine ⟨207281411339753004900843197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138187607559835336600562131 207281411339753004900843197)
        ·
          refine ⟨77730529252407376837816199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207281411339753004900843197 77730529252407376837816199)
          ·
            refine ⟨116595793878611065256724299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77730529252407376837816199 116595793878611065256724299)
            ·
              refine ⟨174893690817916597885086449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116595793878611065256724299 174893690817916597885086449)
              ·
                refine ⟨131170268113437448413814837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174893690817916597885086449 131170268113437448413814837)
                ·
                  refine ⟨12297212635634760788795141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131170268113437448413814837 12297212635634760788795141)
                  ·
                    refine ⟨2305727369181517647899089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12297212635634760788795141 2305727369181517647899089)
                    ·
                      refine ⟨1729295526886138235924317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305727369181517647899089 1729295526886138235924317)
                      ·
                        rfl

theorem cell23_3367791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 4, 2].length) (baseStart_3367791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367791 prefixEnd_3367791 := by exact prefixLift 3367791
  have htrace : WordTrace (prefixWord ++ tailWord_3367791) baseStart_3367791 baseEnd_3367791 := by
    simpa [prefixWord, tailWord_3367791, baseEnd_3367791] using wordTrace_append hprefix tailTrace_3367791
  have hstable : (prefixWord ++ tailWord_3367791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367791).length < 2 ^ (prefixWord ++ tailWord_3367791).sum := by decide
  have hdescent : baseEnd_3367791 < baseStart_3367791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367808 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2]
def baseStart_3367808 : Nat := 118140960795 + 3367808 * 2 ^ 59
def prefixEnd_3367808 : Nat := 4983230072969 + 3 ^ 40 * 3367808 * 2
def baseEnd_3367808 : Nat := 1729304256057264669411739

theorem tailTrace_3367808 : CollatzResearch.WordTrace tailWord_3367808 prefixEnd_3367808 1729304256057264669411739 := by
  unfold tailWord_3367808
  simp only [CollatzResearch.WordTrace]
  refine ⟨61417024491507133329712039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81889365988676177772949385 61417024491507133329712039)
  ·
    refine ⟨92125536737260699994568059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61417024491507133329712039 92125536737260699994568059)
    ·
      refine ⟨138188305105891049991852089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92125536737260699994568059 138188305105891049991852089)
      ·
        refine ⟨103641228829418287493889067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138188305105891049991852089 103641228829418287493889067)
        ·
          refine ⟨155461843244127431240833601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103641228829418287493889067 155461843244127431240833601)
          ·
            refine ⟨116596382433095573430625201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155461843244127431240833601 116596382433095573430625201)
            ·
              refine ⟨87447286824821680072968901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116596382433095573430625201 87447286824821680072968901)
              ·
                refine ⟨16396366279654065013681669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87447286824821680072968901 16396366279654065013681669)
                ·
                  refine ⟨3074318677435137190065313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16396366279654065013681669 3074318677435137190065313)
                  ·
                    refine ⟨2305739008076352892548985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3074318677435137190065313 2305739008076352892548985)
                    ·
                      refine ⟨1729304256057264669411739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305739008076352892548985 1729304256057264669411739)
                      ·
                        rfl

theorem cell23_3367808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 4, 2, 2].length) (baseStart_3367808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367808 prefixEnd_3367808 := by exact prefixLift 3367808
  have htrace : WordTrace (prefixWord ++ tailWord_3367808) baseStart_3367808 baseEnd_3367808 := by
    simpa [prefixWord, tailWord_3367808, baseEnd_3367808] using wordTrace_append hprefix tailTrace_3367808
  have hstable : (prefixWord ++ tailWord_3367808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367808).length < 2 ^ (prefixWord ++ tailWord_3367808).sum := by decide
  have hdescent : baseEnd_3367808 < baseStart_3367808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367842 : List Nat := [3, 3, 1, 2, 2, 1, 2, 3, 2, 2, 2]
def baseStart_3367842 : Nat := 118140960795 + 3367842 * 2 ^ 59
def prefixEnd_3367842 : Nat := 4983230072969 + 3 ^ 40 * 3367842 * 2
def baseEnd_3367842 : Nat := 1729321714399517536386583

theorem tailTrace_3367842 : CollatzResearch.WordTrace tailWord_3367842 prefixEnd_3367842 1729321714399517536386583 := by
  unfold tailWord_3367842
  simp only [CollatzResearch.WordTrace]
  refine ⟨30708822266222772616540445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81890192709927393644107853 30708822266222772616540445)
  ·
    refine ⟨11515808349833539731202667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30708822266222772616540445 11515808349833539731202667)
    ·
      refine ⟨17273712524750309596804001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11515808349833539731202667 17273712524750309596804001)
      ·
        refine ⟨12955284393562732197603001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17273712524750309596804001 12955284393562732197603001)
        ·
          refine ⟨9716463295172049148202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12955284393562732197603001 9716463295172049148202251)
          ·
            refine ⟨14574694942758073722303377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716463295172049148202251 14574694942758073722303377)
            ·
              refine ⟨10931021207068555291727533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14574694942758073722303377 10931021207068555291727533)
              ·
                refine ⟨4099132952650708234397825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10931021207068555291727533 4099132952650708234397825)
                ·
                  refine ⟨3074349714488031175798369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4099132952650708234397825 3074349714488031175798369)
                  ·
                    refine ⟨2305762285866023381848777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3074349714488031175798369 2305762285866023381848777)
                    ·
                      refine ⟨1729321714399517536386583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305762285866023381848777 1729321714399517536386583)
                      ·
                        rfl

theorem cell23_3367842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_3367842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367842 prefixEnd_3367842 := by exact prefixLift 3367842
  have htrace : WordTrace (prefixWord ++ tailWord_3367842) baseStart_3367842 baseEnd_3367842 := by
    simpa [prefixWord, tailWord_3367842, baseEnd_3367842] using wordTrace_append hprefix tailTrace_3367842
  have hstable : (prefixWord ++ tailWord_3367842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367842).length < 2 ^ (prefixWord ++ tailWord_3367842).sum := by decide
  have hdescent : baseEnd_3367842 < baseStart_3367842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367861 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3367861 : Nat := 118140960795 + 3367861 * 2 ^ 59
def prefixEnd_3367861 : Nat := 4983230072969 + 3 ^ 40 * 3367861 * 2
def baseEnd_3367861 : Nat := 576443823510650987349665

theorem tailTrace_3367861 : CollatzResearch.WordTrace tailWord_3367861 prefixEnd_3367861 576443823510650987349665 := by
  unfold tailWord_3367861
  simp only [CollatzResearch.WordTrace]
  refine ⟨122835982051822256711103437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81890654701214837807402291 122835982051822256711103437)
  ·
    refine ⟨46063493269433346266663789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122835982051822256711103437 46063493269433346266663789)
    ·
      refine ⟨17273809976037504849998921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46063493269433346266663789 17273809976037504849998921)
      ·
        refine ⟨12955357482028128637499191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17273809976037504849998921 12955357482028128637499191)
        ·
          refine ⟨19433036223042192956248787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12955357482028128637499191 19433036223042192956248787)
          ·
            refine ⟨29149554334563289434373181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19433036223042192956248787 29149554334563289434373181)
            ·
              refine ⟨10931082875461233537889943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29149554334563289434373181 10931082875461233537889943)
              ·
                refine ⟨16396624313191850306834915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10931082875461233537889943 16396624313191850306834915)
                ·
                  refine ⟨24594936469787775460252373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16396624313191850306834915 24594936469787775460252373)
                  ·
                    refine ⟨576443823510650987349665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24594936469787775460252373 576443823510650987349665)
                    ·
                      rfl

theorem cell23_3367861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3367861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367861 prefixEnd_3367861 := by exact prefixLift 3367861
  have htrace : WordTrace (prefixWord ++ tailWord_3367861) baseStart_3367861 baseEnd_3367861 := by
    simpa [prefixWord, tailWord_3367861, baseEnd_3367861] using wordTrace_append hprefix tailTrace_3367861
  have hstable : (prefixWord ++ tailWord_3367861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367861).length < 2 ^ (prefixWord ++ tailWord_3367861).sum := by decide
  have hdescent : baseEnd_3367861 < baseStart_3367861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367876 : List Nat := [2, 3, 3, 3, 1, 2, 1, 2, 2, 2, 2]
def baseStart_3367876 : Nat := 118140960795 + 3367876 * 2 ^ 59
def prefixEnd_3367876 : Nat := 4983230072969 + 3 ^ 40 * 3367876 * 2
def baseEnd_3367876 : Nat := 1729339172741770403361427

theorem tailTrace_3367876 : CollatzResearch.WordTrace tailWord_3367876 prefixEnd_3367876 1729339172741770403361427 := by
  unfold tailWord_3367876
  simp only [CollatzResearch.WordTrace]
  refine ⟨61418264573383957136449741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81891019431178609515266321 61418264573383957136449741)
  ·
    refine ⟨23031849215018983926168653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61418264573383957136449741 23031849215018983926168653)
    ·
      refine ⟨8636943455632118972313245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23031849215018983926168653 8636943455632118972313245)
      ·
        refine ⟨3238853795862044614617467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8636943455632118972313245 3238853795862044614617467)
        ·
          refine ⟨4858280693793066921926201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3238853795862044614617467 4858280693793066921926201)
          ·
            refine ⟨3643710520344800191444651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858280693793066921926201 3643710520344800191444651)
            ·
              refine ⟨5465565780517200287166977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3643710520344800191444651 5465565780517200287166977)
              ·
                refine ⟨4099174335387900215375233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5465565780517200287166977 4099174335387900215375233)
                ·
                  refine ⟨3074380751540925161531425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4099174335387900215375233 3074380751540925161531425)
                  ·
                    refine ⟨2305785563655693871148569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3074380751540925161531425 2305785563655693871148569)
                    ·
                      refine ⟨1729339172741770403361427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305785563655693871148569 1729339172741770403361427)
                      ·
                        rfl

theorem cell23_3367876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_3367876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367876 prefixEnd_3367876 := by exact prefixLift 3367876
  have htrace : WordTrace (prefixWord ++ tailWord_3367876) baseStart_3367876 baseEnd_3367876 := by
    simpa [prefixWord, tailWord_3367876, baseEnd_3367876] using wordTrace_append hprefix tailTrace_3367876
  have hstable : (prefixWord ++ tailWord_3367876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367876).length < 2 ^ (prefixWord ++ tailWord_3367876).sum := by decide
  have hdescent : baseEnd_3367876 < baseStart_3367876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367921 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 8]
def baseStart_3367921 : Nat := 118140960795 + 3367921 * 2 ^ 59
def prefixEnd_3367921 : Nat := 4983230072969 + 3 ^ 40 * 3367921 * 2
def baseEnd_3367921 : Nat := 192151364374580303033191

theorem tailTrace_3367921 : CollatzResearch.WordTrace tailWord_3367921 prefixEnd_3367921 192151364374580303033191 := by
  unfold tailWord_3367921
  simp only [CollatzResearch.WordTrace]
  refine ⟨122838170431604886958287617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81892113621069924638858411 122838170431604886958287617)
  ·
    refine ⟨92128627823703665218715713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122838170431604886958287617 92128627823703665218715713)
    ·
      refine ⟨69096470867777748914036785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92128627823703665218715713 69096470867777748914036785)
      ·
        refine ⟨51822353150833311685527589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69096470867777748914036785 51822353150833311685527589)
        ·
          refine ⟨9716691215781245941036423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51822353150833311685527589 9716691215781245941036423)
          ·
            refine ⟨14575036823671868911554635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9716691215781245941036423 14575036823671868911554635)
            ·
              refine ⟨21862555235507803367331953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575036823671868911554635 21862555235507803367331953)
              ·
                refine ⟨16396916426630852525498965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21862555235507803367331953 16396916426630852525498965)
                ·
                  refine ⟨192151364374580303033191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16396916426630852525498965 192151364374580303033191)
                  ·
                    rfl

theorem cell23_3367921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_3367921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367921 prefixEnd_3367921 := by exact prefixLift 3367921
  have htrace : WordTrace (prefixWord ++ tailWord_3367921) baseStart_3367921 baseEnd_3367921 := by
    simpa [prefixWord, tailWord_3367921, baseEnd_3367921] using wordTrace_append hprefix tailTrace_3367921
  have hstable : (prefixWord ++ tailWord_3367921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367921).length < 2 ^ (prefixWord ++ tailWord_3367921).sum := by decide
  have hdescent : baseEnd_3367921 < baseStart_3367921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3367985 : List Nat := [1, 2, 2, 3, 1, 2, 5, 1, 1, 5]
def baseStart_3367985 : Nat := 118140960795 + 3367985 * 2 ^ 59
def prefixEnd_3367985 : Nat := 4983230072969 + 3 ^ 40 * 3367985 * 2
def baseEnd_3367985 : Nat := 576465047377703492299475

theorem tailTrace_3367985 : CollatzResearch.WordTrace tailWord_3367985 prefixEnd_3367985 576465047377703492299475 := by
  unfold tailWord_3367985
  simp only [CollatzResearch.WordTrace]
  refine ⟨122840504703373025888617409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81893669802248683925744939 122840504703373025888617409)
  ·
    refine ⟨92130378527529769416463057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122840504703373025888617409 92130378527529769416463057)
    ·
      refine ⟨69097783895647327062347293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92130378527529769416463057 69097783895647327062347293)
      ·
        refine ⟨25911668960867747648380235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69097783895647327062347293 25911668960867747648380235)
        ·
          refine ⟨38867503441301621472570353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25911668960867747648380235 38867503441301621472570353)
          ·
            refine ⟨29150627580976216104427765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38867503441301621472570353 29150627580976216104427765)
            ·
              refine ⟨2732871335716520259790103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29150627580976216104427765 2732871335716520259790103)
              ·
                refine ⟨4099307003574780389685155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2732871335716520259790103 4099307003574780389685155)
                ·
                  refine ⟨6148960505362170584527733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099307003574780389685155 6148960505362170584527733)
                  ·
                    refine ⟨576465047377703492299475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6148960505362170584527733 576465047377703492299475)
                    ·
                      rfl

theorem cell23_3367985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_3367985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3367985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3367985 prefixEnd_3367985 := by exact prefixLift 3367985
  have htrace : WordTrace (prefixWord ++ tailWord_3367985) baseStart_3367985 baseEnd_3367985 := by
    simpa [prefixWord, tailWord_3367985, baseEnd_3367985] using wordTrace_append hprefix tailTrace_3367985
  have hstable : (prefixWord ++ tailWord_3367985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3367985).length < 2 ^ (prefixWord ++ tailWord_3367985).sum := by decide
  have hdescent : baseEnd_3367985 < baseStart_3367985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3367985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368008 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3]
def baseStart_3368008 : Nat := 118140960795 + 3368008 * 2 ^ 59
def prefixEnd_3368008 : Nat := 4983230072969 + 3 ^ 40 * 3368008 * 2
def baseEnd_3368008 : Nat := 1729406952188163886910819

theorem tailTrace_3368008 : CollatzResearch.WordTrace tailWord_3368008 prefixEnd_3368008 1729406952188163886910819 := by
  unfold tailWord_3368008
  simp only [CollatzResearch.WordTrace]
  refine ⟨61420671791144850408352339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81894229054859800544469785 61420671791144850408352339)
  ·
    refine ⟨92131007686717275612528509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61420671791144850408352339 92131007686717275612528509)
    ·
      refine ⟨34549127882518978354698191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92131007686717275612528509 34549127882518978354698191)
      ·
        refine ⟨51823691823778467532047287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34549127882518978354698191 51823691823778467532047287)
        ·
          refine ⟨77735537735667701298070931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51823691823778467532047287 77735537735667701298070931)
          ·
            refine ⟨116603306603501551947106397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77735537735667701298070931 116603306603501551947106397)
            ·
              refine ⟨43726239976313081980164899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116603306603501551947106397 43726239976313081980164899)
              ·
                refine ⟨65589359964469622970247349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43726239976313081980164899 65589359964469622970247349)
                ·
                  refine ⟨6149002496669027153460689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65589359964469622970247349 6149002496669027153460689)
                  ·
                    refine ⟨4611751872501770365095517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6149002496669027153460689 4611751872501770365095517)
                    ·
                      refine ⟨1729406952188163886910819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4611751872501770365095517 1729406952188163886910819)
                      ·
                        rfl

theorem cell23_3368008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_3368008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368008 prefixEnd_3368008 := by exact prefixLift 3368008
  have htrace : WordTrace (prefixWord ++ tailWord_3368008) baseStart_3368008 baseEnd_3368008 := by
    simpa [prefixWord, tailWord_3368008, baseEnd_3368008] using wordTrace_append hprefix tailTrace_3368008
  have hstable : (prefixWord ++ tailWord_3368008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368008).length < 2 ^ (prefixWord ++ tailWord_3368008).sum := by decide
  have hdescent : baseEnd_3368008 < baseStart_3368008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368039 : List Nat := [1, 1, 5, 1, 1, 3, 1, 5, 1, 2, 2]
def baseStart_3368039 : Nat := 118140960795 + 3368039 * 2 ^ 59
def prefixEnd_3368039 : Nat := 4983230072969 + 3 ^ 40 * 3368039 * 2
def baseEnd_3368039 : Nat := 1729422870088453265623177

theorem tailTrace_3368039 : CollatzResearch.WordTrace tailWord_3368039 prefixEnd_3368039 1729422870088453265623177 := by
  unfold tailWord_3368039
  simp only [CollatzResearch.WordTrace]
  refine ⟨122842474245177393111083171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81894982830118262074055447 122842474245177393111083171)
  ·
    refine ⟨184263711367766089666624757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122842474245177393111083171 184263711367766089666624757)
    ·
      refine ⟨17274722940728070906246071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 184263711367766089666624757 17274722940728070906246071)
      ·
        refine ⟨25912084411092106359369107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17274722940728070906246071 25912084411092106359369107)
        ·
          refine ⟨38868126616638159539053661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25912084411092106359369107 38868126616638159539053661)
          ·
            refine ⟨14575547481239309827145123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38868126616638159539053661 14575547481239309827145123)
            ·
              refine ⟨21863321221858964740717685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14575547481239309827145123 21863321221858964740717685)
              ·
                refine ⟨2049686364549277944442283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21863321221858964740717685 2049686364549277944442283)
                ·
                  refine ⟨3074529546823916916663425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049686364549277944442283 3074529546823916916663425)
                  ·
                    refine ⟨2305897160117937687497569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3074529546823916916663425 2305897160117937687497569)
                    ·
                      refine ⟨1729422870088453265623177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2305897160117937687497569 1729422870088453265623177)
                      ·
                        rfl

theorem cell23_3368039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_3368039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368039 prefixEnd_3368039 := by exact prefixLift 3368039
  have htrace : WordTrace (prefixWord ++ tailWord_3368039) baseStart_3368039 baseEnd_3368039 := by
    simpa [prefixWord, tailWord_3368039, baseEnd_3368039] using wordTrace_append hprefix tailTrace_3368039
  have hstable : (prefixWord ++ tailWord_3368039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368039).length < 2 ^ (prefixWord ++ tailWord_3368039).sum := by decide
  have hdescent : baseEnd_3368039 < baseStart_3368039 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368042 : List Nat := [3, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_3368042 : Nat := 118140960795 + 3368042 * 2 ^ 59
def prefixEnd_3368042 : Nat := 4983230072969 + 3 ^ 40 * 3368042 * 2
def baseEnd_3368042 : Nat := 1729424410530416753885663

theorem tailTrace_3368042 : CollatzResearch.WordTrace tailWord_3368042 prefixEnd_3368042 1729424410530416753885663 := by
  unfold tailWord_3368042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30710645916041631155860595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81895055776111016415628253 30710645916041631155860595)
  ·
    refine ⟨46065968874062446733790893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30710645916041631155860595 46065968874062446733790893)
    ·
      refine ⟨17274738327773417525171585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46065968874062446733790893 17274738327773417525171585)
      ·
        refine ⟨12956053745830063143878689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17274738327773417525171585 12956053745830063143878689)
        ·
          refine ⟨9717040309372547357909017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12956053745830063143878689 9717040309372547357909017)
          ·
            refine ⟨7287780232029410518431763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9717040309372547357909017 7287780232029410518431763)
            ·
              refine ⟨10931670348044115777647645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7287780232029410518431763 10931670348044115777647645)
              ·
                refine ⟨4099376380516543416617867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10931670348044115777647645 4099376380516543416617867)
                ·
                  refine ⟨6149064570774815124926801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099376380516543416617867 6149064570774815124926801)
                  ·
                    refine ⟨4611798428081111343695101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6149064570774815124926801 4611798428081111343695101)
                    ·
                      refine ⟨1729424410530416753885663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4611798428081111343695101 1729424410530416753885663)
                      ·
                        rfl

theorem cell23_3368042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_3368042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368042 prefixEnd_3368042 := by exact prefixLift 3368042
  have htrace : WordTrace (prefixWord ++ tailWord_3368042) baseStart_3368042 baseEnd_3368042 := by
    simpa [prefixWord, tailWord_3368042, baseEnd_3368042] using wordTrace_append hprefix tailTrace_3368042
  have hstable : (prefixWord ++ tailWord_3368042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368042).length < 2 ^ (prefixWord ++ tailWord_3368042).sum := by decide
  have hdescent : baseEnd_3368042 < baseStart_3368042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368055 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_3368055 : Nat := 118140960795 + 3368055 * 2 ^ 59
def prefixEnd_3368055 : Nat := 4983230072969 + 3 ^ 40 * 3368055 * 2
def baseEnd_3368055 : Nat := 1729431085778925203023103

theorem tailTrace_3368055 : CollatzResearch.WordTrace tailWord_3368055 prefixEnd_3368055 1729431085778925203023103 := by
  unfold tailWord_3368055
  simp only [CollatzResearch.WordTrace]
  refine ⟨122843057813119427843665619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81895371875412951895777079 122843057813119427843665619)
  ·
    refine ⟨184264586719679141765498429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122843057813119427843665619 184264586719679141765498429)
    ·
      refine ⟨69099220019879678162061911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184264586719679141765498429 69099220019879678162061911)
      ·
        refine ⟨103648830029819517243092867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69099220019879678162061911 103648830029819517243092867)
        ·
          refine ⟨155473245044729275864639301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103648830029819517243092867 155473245044729275864639301)
          ·
            refine ⟨29151233445886739224619869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155473245044729275864639301 29151233445886739224619869)
            ·
              refine ⟨10931712542207527209232451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29151233445886739224619869 10931712542207527209232451)
              ·
                refine ⟨16397568813311290813848677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10931712542207527209232451 16397568813311290813848677)
                ·
                  refine ⟨3074544152495867027596627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16397568813311290813848677 3074544152495867027596627)
                  ·
                    refine ⟨4611816228743800541394941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3074544152495867027596627 4611816228743800541394941)
                    ·
                      refine ⟨1729431085778925203023103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4611816228743800541394941 1729431085778925203023103)
                      ·
                        rfl

theorem cell23_3368055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_3368055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368055 prefixEnd_3368055 := by exact prefixLift 3368055
  have htrace : WordTrace (prefixWord ++ tailWord_3368055) baseStart_3368055 baseEnd_3368055 := by
    simpa [prefixWord, tailWord_3368055, baseEnd_3368055] using wordTrace_append hprefix tailTrace_3368055
  have hstable : (prefixWord ++ tailWord_3368055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368055).length < 2 ^ (prefixWord ++ tailWord_3368055).sum := by decide
  have hdescent : baseEnd_3368055 < baseStart_3368055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368108 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_3368108 : Nat := 118140960795 + 3368108 * 2 ^ 59
def prefixEnd_3368108 : Nat := 4983230072969 + 3 ^ 40 * 3368108 * 2
def baseEnd_3368108 : Nat := 1729458300253613495660359

theorem tailTrace_3368108 : CollatzResearch.WordTrace tailWord_3368108 prefixEnd_3368108 1729458300253613495660359 := by
  unfold tailWord_3368108
  simp only [CollatzResearch.WordTrace]
  refine ⟨61422495440963708947672489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81896660587951611930229985 61422495440963708947672489)
  ·
    refine ⟨46066871580722781710754367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61422495440963708947672489 46066871580722781710754367)
    ·
      refine ⟨69100307371084172566131551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46066871580722781710754367 69100307371084172566131551)
      ·
        refine ⟨103650461056626258849197327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69100307371084172566131551 103650461056626258849197327)
        ·
          refine ⟨155475691584939388273795991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103650461056626258849197327 155475691584939388273795991)
          ·
            refine ⟨233213537377409082410693987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155475691584939388273795991 233213537377409082410693987)
            ·
              refine ⟨349820306066113623616040981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233213537377409082410693987 349820306066113623616040981)
              ·
                refine ⟨16397826846849076107001921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 349820306066113623616040981 16397826846849076107001921)
                ·
                  refine ⟨12298370135136807080251441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16397826846849076107001921 12298370135136807080251441)
                  ·
                    refine ⟨9223777601352605310188581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12298370135136807080251441 9223777601352605310188581)
                    ·
                      refine ⟨1729458300253613495660359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9223777601352605310188581 1729458300253613495660359)
                      ·
                        rfl

theorem cell23_3368108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_3368108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368108 prefixEnd_3368108 := by exact prefixLift 3368108
  have htrace : WordTrace (prefixWord ++ tailWord_3368108) baseStart_3368108 baseEnd_3368108 := by
    simpa [prefixWord, tailWord_3368108, baseEnd_3368108] using wordTrace_append hprefix tailTrace_3368108
  have hstable : (prefixWord ++ tailWord_3368108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368108).length < 2 ^ (prefixWord ++ tailWord_3368108).sum := by decide
  have hdescent : baseEnd_3368108 < baseStart_3368108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368195 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 5, 4]
def baseStart_3368195 : Nat := 118140960795 + 3368195 * 2 ^ 59
def prefixEnd_3368195 : Nat := 4983230072969 + 3 ^ 40 * 3368195 * 2
def baseEnd_3368195 : Nat := 576500991023518218424153

theorem tailTrace_3368195 : CollatzResearch.WordTrace tailWord_3368195 prefixEnd_3368195 576500991023518218424153 := by
  unfold tailWord_3368195
  simp only [CollatzResearch.WordTrace]
  refine ⟨122848164032612231753762039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81898776021741487835841359 122848164032612231753762039)
  ·
    refine ⟨184272246048918347630643059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122848164032612231753762039 184272246048918347630643059)
    ·
      refine ⟨276408369073377521445964589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184272246048918347630643059 276408369073377521445964589)
      ·
        refine ⟨103653138402516570542236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276408369073377521445964589 103653138402516570542236721)
        ·
          refine ⟨77739853801887427906677541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103653138402516570542236721 77739853801887427906677541)
          ·
            refine ⟨14576222587853892732502039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77739853801887427906677541 14576222587853892732502039)
            ·
              refine ⟨21864333881780839098753059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576222587853892732502039 21864333881780839098753059)
              ·
                refine ⟨32796500822671258648129589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21864333881780839098753059 32796500822671258648129589)
                ·
                  refine ⟨3074671952125430498262149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32796500822671258648129589 3074671952125430498262149)
                  ·
                    refine ⟨576500991023518218424153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074671952125430498262149 576500991023518218424153)
                    ·
                      rfl

theorem cell23_3368195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 5, 4].length) (baseStart_3368195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368195 prefixEnd_3368195 := by exact prefixLift 3368195
  have htrace : WordTrace (prefixWord ++ tailWord_3368195) baseStart_3368195 baseEnd_3368195 := by
    simpa [prefixWord, tailWord_3368195, baseEnd_3368195] using wordTrace_append hprefix tailTrace_3368195
  have hstable : (prefixWord ++ tailWord_3368195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368195).length < 2 ^ (prefixWord ++ tailWord_3368195).sum := by decide
  have hdescent : baseEnd_3368195 < baseStart_3368195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368229 : List Nat := [1, 3, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_3368229 : Nat := 118140960795 + 3368229 * 2 ^ 59
def prefixEnd_3368229 : Nat := 4983230072969 + 3 ^ 40 * 3368229 * 2
def baseEnd_3368229 : Nat := 576506810470935840749101

theorem tailTrace_3368229 : CollatzResearch.WordTrace tailWord_3368229 prefixEnd_3368229 576506810470935840749101 := by
  unfold tailWord_3368229
  simp only [CollatzResearch.WordTrace]
  refine ⟨122849404114489055560499741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81899602742992703706999827 122849404114489055560499741)
  ·
    refine ⟨46068526542933395835187403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122849404114489055560499741 46068526542933395835187403)
    ·
      refine ⟨69102789814400093752781105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46068526542933395835187403 69102789814400093752781105)
      ·
        refine ⟨51827092360800070314585829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69102789814400093752781105 51827092360800070314585829)
        ·
          refine ⟨9717579817650013183984843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51827092360800070314585829 9717579817650013183984843)
          ·
            refine ⟨14576369726475019775977265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9717579817650013183984843 14576369726475019775977265)
            ·
              refine ⟨10932277294856264831982949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14576369726475019775977265 10932277294856264831982949)
              ·
                refine ⟨2049801992785549655996803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10932277294856264831982949 2049801992785549655996803)
                ·
                  refine ⟨3074702989178324483995205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2049801992785549655996803 3074702989178324483995205)
                  ·
                    refine ⟨576506810470935840749101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3074702989178324483995205 576506810470935840749101)
                    ·
                      rfl

theorem cell23_3368229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_3368229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368229 prefixEnd_3368229 := by exact prefixLift 3368229
  have htrace : WordTrace (prefixWord ++ tailWord_3368229) baseStart_3368229 baseEnd_3368229 := by
    simpa [prefixWord, tailWord_3368229, baseEnd_3368229] using wordTrace_append hprefix tailTrace_3368229
  have hstable : (prefixWord ++ tailWord_3368229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368229).length < 2 ^ (prefixWord ++ tailWord_3368229).sum := by decide
  have hdescent : baseEnd_3368229 < baseStart_3368229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368279 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 2, 3, 2]
def baseStart_3368279 : Nat := 118140960795 + 3368279 * 2 ^ 59
def prefixEnd_3368279 : Nat := 4983230072969 + 3 ^ 40 * 3368279 * 2
def baseEnd_3368279 : Nat := 1729546105445532326622073

theorem tailTrace_3368279 : CollatzResearch.WordTrace tailWord_3368279 prefixEnd_3368279 1729546105445532326622073 := by
  unfold tailWord_3368279
  simp only [CollatzResearch.WordTrace]
  refine ⟨122851227764307914099819891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81900818509538609399879927 122851227764307914099819891)
  ·
    refine ⟨184276841646461871149729837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122851227764307914099819891 184276841646461871149729837)
    ·
      refine ⟨69103815617423201681148689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184276841646461871149729837 69103815617423201681148689)
      ·
        refine ⟨51827861713067401260861517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69103815617423201681148689 51827861713067401260861517)
        ·
          refine ⟨19435448142400275472823069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51827861713067401260861517 19435448142400275472823069)
          ·
            refine ⟨7288293053400103302308651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19435448142400275472823069 7288293053400103302308651)
            ·
              refine ⟨10932439580100154953462977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288293053400103302308651 10932439580100154953462977)
              ·
                refine ⟨8199329685075116215097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10932439580100154953462977 8199329685075116215097233)
                ·
                  refine ⟨6149497263806337161322925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8199329685075116215097233 6149497263806337161322925)
                  ·
                    refine ⟨2306061473927376435496097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6149497263806337161322925 2306061473927376435496097)
                    ·
                      refine ⟨1729546105445532326622073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306061473927376435496097 1729546105445532326622073)
                      ·
                        rfl

theorem cell23_3368279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_3368279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368279 prefixEnd_3368279 := by exact prefixLift 3368279
  have htrace : WordTrace (prefixWord ++ tailWord_3368279) baseStart_3368279 baseEnd_3368279 := by
    simpa [prefixWord, tailWord_3368279, baseEnd_3368279] using wordTrace_append hprefix tailTrace_3368279
  have hstable : (prefixWord ++ tailWord_3368279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368279).length < 2 ^ (prefixWord ++ tailWord_3368279).sum := by decide
  have hdescent : baseEnd_3368279 < baseStart_3368279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368305 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 6]
def baseStart_3368305 : Nat := 118140960795 + 3368305 * 2 ^ 59
def prefixEnd_3368305 : Nat := 4983230072969 + 3 ^ 40 * 3368305 * 2
def baseEnd_3368305 : Nat := 1729559455942549224896953

theorem tailTrace_3368305 : CollatzResearch.WordTrace tailWord_3368305 prefixEnd_3368305 1729559455942549224896953 := by
  unfold tailWord_3368305
  simp only [CollatzResearch.WordTrace]
  refine ⟨122852176062213720540266369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81901450708142480360177579 122852176062213720540266369)
  ·
    refine ⟨92139132046660290405199777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122852176062213720540266369 92139132046660290405199777)
    ·
      refine ⟨69104349034995217803899833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92139132046660290405199777 69104349034995217803899833)
      ·
        refine ⟨51828261776246413352924875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69104349034995217803899833 51828261776246413352924875)
        ·
          refine ⟨77742392664369620029387313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51828261776246413352924875 77742392664369620029387313)
          ·
            refine ⟨58306794498277215022040485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77742392664369620029387313 58306794498277215022040485)
            ·
              refine ⟨10932523968426977816632591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58306794498277215022040485 10932523968426977816632591)
              ·
                refine ⟨16398785952640466724948887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932523968426977816632591 16398785952640466724948887)
                ·
                  refine ⟨24598178928960700087423331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16398785952640466724948887 24598178928960700087423331)
                  ·
                    refine ⟨36897268393441050131134997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24598178928960700087423331 36897268393441050131134997)
                    ·
                      refine ⟨1729559455942549224896953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36897268393441050131134997 1729559455942549224896953)
                      ·
                        rfl

theorem cell23_3368305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_3368305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368305 prefixEnd_3368305 := by exact prefixLift 3368305
  have htrace : WordTrace (prefixWord ++ tailWord_3368305) baseStart_3368305 baseEnd_3368305 := by
    simpa [prefixWord, tailWord_3368305, baseEnd_3368305] using wordTrace_append hprefix tailTrace_3368305
  have hstable : (prefixWord ++ tailWord_3368305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368305).length < 2 ^ (prefixWord ++ tailWord_3368305).sum := by decide
  have hdescent : baseEnd_3368305 < baseStart_3368305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368309 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_3368309 : Nat := 118140960795 + 3368309 * 2 ^ 59
def prefixEnd_3368309 : Nat := 4983230072969 + 3 ^ 40 * 3368309 * 2
def baseEnd_3368309 : Nat := 1729561509865167209246935

theorem tailTrace_3368309 : CollatzResearch.WordTrace tailWord_3368309 prefixEnd_3368309 1729561509865167209246935 := by
  unfold tailWord_3368309
  simp only [CollatzResearch.WordTrace]
  refine ⟨122852321954199229223411981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81901547969466152815607987 122852321954199229223411981)
  ·
    refine ⟨46069620732824710958779493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122852321954199229223411981 46069620732824710958779493)
    ·
      refine ⟨8638053887404633304771155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46069620732824710958779493 8638053887404633304771155)
      ·
        refine ⟨12957080831106949957156733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638053887404633304771155 12957080831106949957156733)
        ·
          refine ⟨4858905311665106233933775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12957080831106949957156733 4858905311665106233933775)
          ·
            refine ⟨7288357967497659350900663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4858905311665106233933775 7288357967497659350900663)
            ·
              refine ⟨10932536951246489026350995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7288357967497659350900663 10932536951246489026350995)
              ·
                refine ⟨16398805426869733539526493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10932536951246489026350995 16398805426869733539526493)
                ·
                  refine ⟨6149552035076150077322435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16398805426869733539526493 6149552035076150077322435)
                  ·
                    refine ⟨9224328052614225115983653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6149552035076150077322435 9224328052614225115983653)
                    ·
                      refine ⟨1729561509865167209246935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9224328052614225115983653 1729561509865167209246935)
                      ·
                        rfl

theorem cell23_3368309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_3368309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368309 prefixEnd_3368309 := by exact prefixLift 3368309
  have htrace : WordTrace (prefixWord ++ tailWord_3368309) baseStart_3368309 baseEnd_3368309 := by
    simpa [prefixWord, tailWord_3368309, baseEnd_3368309] using wordTrace_append hprefix tailTrace_3368309
  have hstable : (prefixWord ++ tailWord_3368309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368309).length < 2 ^ (prefixWord ++ tailWord_3368309).sum := by decide
  have hdescent : baseEnd_3368309 < baseStart_3368309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368329 : List Nat := [1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 5]
def baseStart_3368329 : Nat := 118140960795 + 3368329 * 2 ^ 59
def prefixEnd_3368329 : Nat := 4983230072969 + 3 ^ 40 * 3368329 * 2
def baseEnd_3368329 : Nat := 1729571779478257130996843

theorem tailTrace_3368329 : CollatzResearch.WordTrace tailWord_3368329 prefixEnd_3368329 1729571779478257130996843 := by
  unfold tailWord_3368329
  simp only [CollatzResearch.WordTrace]
  refine ⟨122853051414126772639140041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81902034276084515092760027 122853051414126772639140041)
  ·
    refine ⟨92139788560595079479355031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122853051414126772639140041 92139788560595079479355031)
    ·
      refine ⟨138209682840892619219032547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92139788560595079479355031 138209682840892619219032547)
      ·
        refine ⟨207314524261338928828548821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138209682840892619219032547 207314524261338928828548821)
        ·
          refine ⟨4858934162375131144419113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 207314524261338928828548821 4858934162375131144419113)
          ·
            refine ⟨3644200621781348358314335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4858934162375131144419113 3644200621781348358314335)
            ·
              refine ⟨5466300932672022537471503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644200621781348358314335 5466300932672022537471503)
              ·
                refine ⟨8199451399008033806207255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466300932672022537471503 8199451399008033806207255)
                ·
                  refine ⟨12299177098512050709310883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199451399008033806207255 12299177098512050709310883)
                  ·
                    refine ⟨18448765647768076063966325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12299177098512050709310883 18448765647768076063966325)
                    ·
                      refine ⟨1729571779478257130996843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18448765647768076063966325 1729571779478257130996843)
                      ·
                        rfl

theorem cell23_3368329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 1, 5].length) (baseStart_3368329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368329 prefixEnd_3368329 := by exact prefixLift 3368329
  have htrace : WordTrace (prefixWord ++ tailWord_3368329) baseStart_3368329 baseEnd_3368329 := by
    simpa [prefixWord, tailWord_3368329, baseEnd_3368329] using wordTrace_append hprefix tailTrace_3368329
  have hstable : (prefixWord ++ tailWord_3368329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368329).length < 2 ^ (prefixWord ++ tailWord_3368329).sum := by decide
  have hdescent : baseEnd_3368329 < baseStart_3368329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368345 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_3368345 : Nat := 118140960795 + 3368345 * 2 ^ 59
def prefixEnd_3368345 : Nat := 4983230072969 + 3 ^ 40 * 3368345 * 2
def baseEnd_3368345 : Nat := 576526665056243022798923

theorem tailTrace_3368345 : CollatzResearch.WordTrace tailWord_3368345 prefixEnd_3368345 576526665056243022798923 := by
  unfold tailWord_3368345
  simp only [CollatzResearch.WordTrace]
  refine ⟨122853634982068807371722489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81902423321379204914481659 122853634982068807371722489)
  ·
    refine ⟨92140226236551605528791867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122853634982068807371722489 92140226236551605528791867)
    ·
      refine ⟨138210339354827408293187801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92140226236551605528791867 138210339354827408293187801)
      ·
        refine ⟨103657754516120556219890851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138210339354827408293187801 103657754516120556219890851)
        ·
          refine ⟨155486631774180834329836277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103657754516120556219890851 155486631774180834329836277)
          ·
            refine ⟨14576871728829453218422151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155486631774180834329836277 14576871728829453218422151)
            ·
              refine ⟨21865307593244179827633227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14576871728829453218422151 21865307593244179827633227)
              ·
                refine ⟨32797961389866269741449841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21865307593244179827633227 32797961389866269741449841)
                ·
                  refine ⟨24598471042399702306087381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32797961389866269741449841 24598471042399702306087381)
                  ·
                    refine ⟨576526665056243022798923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24598471042399702306087381 576526665056243022798923)
                    ·
                      rfl

theorem cell23_3368345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_3368345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368345 prefixEnd_3368345 := by exact prefixLift 3368345
  have htrace : WordTrace (prefixWord ++ tailWord_3368345) baseStart_3368345 baseEnd_3368345 := by
    simpa [prefixWord, tailWord_3368345, baseEnd_3368345] using wordTrace_append hprefix tailTrace_3368345
  have hstable : (prefixWord ++ tailWord_3368345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368345).length < 2 ^ (prefixWord ++ tailWord_3368345).sum := by decide
  have hdescent : baseEnd_3368345 < baseStart_3368345 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368359 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_3368359 : Nat := 118140960795 + 3368359 * 2 ^ 59
def prefixEnd_3368359 : Nat := 4983230072969 + 3 ^ 40 * 3368359 * 2
def baseEnd_3368359 : Nat := 1729587183897892013621705

theorem tailTrace_3368359 : CollatzResearch.WordTrace tailWord_3368359 prefixEnd_3368359 1729587183897892013621705 := by
  unfold tailWord_3368359
  simp only [CollatzResearch.WordTrace]
  refine ⟨122854145604018087762732131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81902763736012058508488087 122854145604018087762732131)
  ·
    refine ⟨184281218406027131644098197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122854145604018087762732131 184281218406027131644098197)
    ·
      refine ⟨8638182112782521795817103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184281218406027131644098197 8638182112782521795817103)
      ·
        refine ⟨12957273169173782693725655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8638182112782521795817103 12957273169173782693725655)
        ·
          refine ⟨19435909753760674040588483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957273169173782693725655 19435909753760674040588483)
          ·
            refine ⟨29153864630641011060882725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19435909753760674040588483 29153864630641011060882725)
            ·
              refine ⟨5466349618245189573915511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29153864630641011060882725 5466349618245189573915511)
              ·
                refine ⟨8199524427367784360873267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466349618245189573915511 8199524427367784360873267)
                ·
                  refine ⟨12299286641051676541309901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8199524427367784360873267 12299286641051676541309901)
                  ·
                    refine ⟨4612232490394378702991213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12299286641051676541309901 4612232490394378702991213)
                    ·
                      refine ⟨1729587183897892013621705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612232490394378702991213 1729587183897892013621705)
                      ·
                        rfl

theorem cell23_3368359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_3368359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368359 prefixEnd_3368359 := by exact prefixLift 3368359
  have htrace : WordTrace (prefixWord ++ tailWord_3368359) baseStart_3368359 baseEnd_3368359 := by
    simpa [prefixWord, tailWord_3368359, baseEnd_3368359] using wordTrace_append hprefix tailTrace_3368359
  have hstable : (prefixWord ++ tailWord_3368359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368359).length < 2 ^ (prefixWord ++ tailWord_3368359).sum := by decide
  have hdescent : baseEnd_3368359 < baseStart_3368359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368369 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 3, 3, 2]
def baseStart_3368369 : Nat := 118140960795 + 3368369 * 2 ^ 59
def prefixEnd_3368369 : Nat := 4983230072969 + 3 ^ 40 * 3368369 * 2
def baseEnd_3368369 : Nat := 1729592318704436974496659

theorem tailTrace_3368369 : CollatzResearch.WordTrace tailWord_3368369 prefixEnd_3368369 1729592318704436974496659 := by
  unfold tailWord_3368369
  simp only [CollatzResearch.WordTrace]
  refine ⟨122854510333981859470596161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81903006889321239647064107 122854510333981859470596161)
  ·
    refine ⟨92140882750486394602947121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122854510333981859470596161 92140882750486394602947121)
    ·
      refine ⟨69105662062864795952210341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92140882750486394602947121 69105662062864795952210341)
      ·
        refine ⟨12957311636787149241039439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69105662062864795952210341 12957311636787149241039439)
        ·
          refine ⟨19435967455180723861559159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12957311636787149241039439 19435967455180723861559159)
          ·
            refine ⟨29153951182771085792338739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19435967455180723861559159 29153951182771085792338739)
            ·
              refine ⟨43730926774156628688508109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29153951182771085792338739 43730926774156628688508109)
              ·
                refine ⟨16399097540308735758190541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43730926774156628688508109 16399097540308735758190541)
                ·
                  refine ⟨6149661577615775909321453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16399097540308735758190541 6149661577615775909321453)
                  ·
                    refine ⟨2306123091605915965995545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6149661577615775909321453 2306123091605915965995545)
                    ·
                      refine ⟨1729592318704436974496659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306123091605915965995545 1729592318704436974496659)
                      ·
                        rfl

theorem cell23_3368369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_3368369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368369 prefixEnd_3368369 := by exact prefixLift 3368369
  have htrace : WordTrace (prefixWord ++ tailWord_3368369) baseStart_3368369 baseEnd_3368369 := by
    simpa [prefixWord, tailWord_3368369, baseEnd_3368369] using wordTrace_append hprefix tailTrace_3368369
  have hstable : (prefixWord ++ tailWord_3368369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368369).length < 2 ^ (prefixWord ++ tailWord_3368369).sum := by decide
  have hdescent : baseEnd_3368369 < baseStart_3368369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368375 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 1, 8]
def baseStart_3368375 : Nat := 118140960795 + 3368375 * 2 ^ 59
def prefixEnd_3368375 : Nat := 4983230072969 + 3 ^ 40 * 3368375 * 2
def baseEnd_3368375 : Nat := 576531799862787983673877

theorem tailTrace_3368375 : CollatzResearch.WordTrace tailWord_3368375 prefixEnd_3368375 576531799862787983673877 := by
  unfold tailWord_3368375
  simp only [CollatzResearch.WordTrace]
  refine ⟨122854729171960122495314579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81903152781306748330209719 122854729171960122495314579)
  ·
    refine ⟨184282093757940183742971869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122854729171960122495314579 184282093757940183742971869)
    ·
      refine ⟨69105785159227568903614451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184282093757940183742971869 69105785159227568903614451)
      ·
        refine ⟨103658677738841353355421677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69105785159227568903614451 103658677738841353355421677)
        ·
          refine ⟨38872004152065507508283129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103658677738841353355421677 38872004152065507508283129)
          ·
            refine ⟨29154003114049130631212347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38872004152065507508283129 29154003114049130631212347)
            ·
              refine ⟨43731004671073695946818521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29154003114049130631212347 43731004671073695946818521)
              ·
                refine ⟨32798253503305271960113891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43731004671073695946818521 32798253503305271960113891)
                ·
                  refine ⟨49197380254957907940170837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32798253503305271960113891 49197380254957907940170837)
                  ·
                    refine ⟨576531799862787983673877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49197380254957907940170837 576531799862787983673877)
                    ·
                      rfl

theorem cell23_3368375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_3368375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368375 prefixEnd_3368375 := by exact prefixLift 3368375
  have htrace : WordTrace (prefixWord ++ tailWord_3368375) baseStart_3368375 baseEnd_3368375 := by
    simpa [prefixWord, tailWord_3368375, baseEnd_3368375] using wordTrace_append hprefix tailTrace_3368375
  have hstable : (prefixWord ++ tailWord_3368375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368375).length < 2 ^ (prefixWord ++ tailWord_3368375).sum := by decide
  have hdescent : baseEnd_3368375 < baseStart_3368375 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368380 : List Nat := [2, 2, 2, 4, 3, 1, 2, 1, 1, 2, 3]
def baseStart_3368380 : Nat := 118140960795 + 3368380 * 2 ^ 59
def prefixEnd_3368380 : Nat := 4983230072969 + 3 ^ 40 * 3368380 * 2
def baseEnd_3368380 : Nat := 1729597966991636431459109

theorem tailTrace_3368380 : CollatzResearch.WordTrace tailWord_3368380 prefixEnd_3368380 1729597966991636431459109 := by
  unfold tailWord_3368380
  simp only [CollatzResearch.WordTrace]
  refine ⟨61427455768471004174623297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81903274357961338899497729 61427455768471004174623297)
  ·
    refine ⟨46070591826353253130967473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61427455768471004174623297 46070591826353253130967473)
    ·
      refine ⟨34552943869764939848225605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46070591826353253130967473 34552943869764939848225605)
      ·
        refine ⟨6478676975580926221542301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34552943869764939848225605 6478676975580926221542301)
        ·
          refine ⟨2429503865842847333078363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6478676975580926221542301 2429503865842847333078363)
          ·
            refine ⟨3644255798764270999617545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2429503865842847333078363 3644255798764270999617545)
            ·
              refine ⟨2733191849073203249713159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3644255798764270999617545 2733191849073203249713159)
              ·
                refine ⟨4099787773609804874569739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733191849073203249713159 4099787773609804874569739)
                ·
                  refine ⟨6149681660414707311854609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4099787773609804874569739 6149681660414707311854609)
                  ·
                    refine ⟨4612261245311030483890957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6149681660414707311854609 4612261245311030483890957)
                    ·
                      refine ⟨1729597966991636431459109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612261245311030483890957 1729597966991636431459109)
                      ·
                        rfl

theorem cell23_3368380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_3368380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368380 prefixEnd_3368380 := by exact prefixLift 3368380
  have htrace : WordTrace (prefixWord ++ tailWord_3368380) baseStart_3368380 baseEnd_3368380 := by
    simpa [prefixWord, tailWord_3368380, baseEnd_3368380] using wordTrace_append hprefix tailTrace_3368380
  have hstable : (prefixWord ++ tailWord_3368380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368380).length < 2 ^ (prefixWord ++ tailWord_3368380).sum := by decide
  have hdescent : baseEnd_3368380 < baseStart_3368380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368425 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 6]
def baseStart_3368425 : Nat := 118140960795 + 3368425 * 2 ^ 59
def prefixEnd_3368425 : Nat := 4983230072969 + 3 ^ 40 * 3368425 * 2
def baseEnd_3368425 : Nat := 1729621073621088755396401

theorem tailTrace_3368425 : CollatzResearch.WordTrace tailWord_3368425 prefixEnd_3368425 1729621073621088755396401 := by
  unfold tailWord_3368425
  simp only [CollatzResearch.WordTrace]
  refine ⟨122856552821778981034634729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81904368547852654023089819 122856552821778981034634729)
  ·
    refine ⟨92142414616334235775976047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122856552821778981034634729 92142414616334235775976047)
    ·
      refine ⟨138213621924501353663964071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92142414616334235775976047 138213621924501353663964071)
      ·
        refine ⟨207320432886752030495946107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138213621924501353663964071 207320432886752030495946107)
        ·
          refine ⟨310980649330128045743919161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207320432886752030495946107 310980649330128045743919161)
          ·
            refine ⟨233235486997596034307939371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310980649330128045743919161 233235486997596034307939371)
            ·
              refine ⟨349853230496394051461909057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233235486997596034307939371 349853230496394051461909057)
              ·
                refine ⟨262389922872295538596431793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349853230496394051461909057 262389922872295538596431793)
                ·
                  refine ⟨196792442154221653947323845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 262389922872295538596431793 196792442154221653947323845)
                  ·
                    refine ⟨36898582903916560115123221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 196792442154221653947323845 36898582903916560115123221)
                    ·
                      refine ⟨1729621073621088755396401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36898582903916560115123221 1729621073621088755396401)
                      ·
                        rfl

theorem cell23_3368425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_3368425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368425 prefixEnd_3368425 := by exact prefixLift 3368425
  have htrace : WordTrace (prefixWord ++ tailWord_3368425) baseStart_3368425 baseEnd_3368425 := by
    simpa [prefixWord, tailWord_3368425, baseEnd_3368425] using wordTrace_append hprefix tailTrace_3368425
  have hstable : (prefixWord ++ tailWord_3368425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368425).length < 2 ^ (prefixWord ++ tailWord_3368425).sum := by decide
  have hdescent : baseEnd_3368425 < baseStart_3368425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368482 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 2, 8]
def baseStart_3368482 : Nat := 118140960795 + 3368482 * 2 ^ 59
def prefixEnd_3368482 : Nat := 4983230072969 + 3 ^ 40 * 3368482 * 2
def baseEnd_3368482 : Nat := 576550114006131677461213

theorem tailTrace_3368482 : CollatzResearch.WordTrace tailWord_3368482 prefixEnd_3368482 576550114006131677461213 := by
  unfold tailWord_3368482
  simp only [CollatzResearch.WordTrace]
  refine ⟨30714657945643119942364925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81905754521714986512973133 30714657945643119942364925)
  ·
    refine ⟨11517996729616169978386847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30714657945643119942364925 11517996729616169978386847)
    ·
      refine ⟨17276995094424254967580271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11517996729616169978386847 17276995094424254967580271)
      ·
        refine ⟨25915492641636382451370407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17276995094424254967580271 25915492641636382451370407)
        ·
          refine ⟨38873238962454573677055611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25915492641636382451370407 38873238962454573677055611)
          ·
            refine ⟨58309858443681860515583417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38873238962454573677055611 58309858443681860515583417)
            ·
              refine ⟨43732393832761395386687563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58309858443681860515583417 43732393832761395386687563)
              ·
                refine ⟨65598590749142093080031345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43732393832761395386687563 65598590749142093080031345)
                ·
                  refine ⟨49198943061856569810023509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65598590749142093080031345 49198943061856569810023509)
                  ·
                    refine ⟨576550114006131677461213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 49198943061856569810023509 576550114006131677461213)
                    ·
                      rfl

theorem cell23_3368482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_3368482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368482 prefixEnd_3368482 := by exact prefixLift 3368482
  have htrace : WordTrace (prefixWord ++ tailWord_3368482) baseStart_3368482 baseEnd_3368482 := by
    simpa [prefixWord, tailWord_3368482, baseEnd_3368482] using wordTrace_append hprefix tailTrace_3368482
  have hstable : (prefixWord ++ tailWord_3368482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368482).length < 2 ^ (prefixWord ++ tailWord_3368482).sum := by decide
  have hdescent : baseEnd_3368482 < baseStart_3368482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368573 : List Nat := [1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 3]
def baseStart_3368573 : Nat := 118140960795 + 3368573 * 2 ^ 59
def prefixEnd_3368573 : Nat := 4983230072969 + 3 ^ 40 * 3368573 * 2
def baseEnd_3368573 : Nat := 1729697068757954176345721

theorem tailTrace_3368573 : CollatzResearch.WordTrace tailWord_3368573 prefixEnd_3368573 1729697068757954176345721 := by
  unfold tailWord_3368573
  simp only [CollatzResearch.WordTrace]
  refine ⟨122861950825242802311022373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81907967216828534874014915 122861950825242802311022373)
  ·
    refine ⟨23036615779733025433316695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122861950825242802311022373 23036615779733025433316695)
    ·
      refine ⟨34554923669599538149975043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23036615779733025433316695 34554923669599538149975043)
      ·
        refine ⟨51832385504399307224962565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34554923669599538149975043 51832385504399307224962565)
        ·
          refine ⟨9718572282074870104680481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51832385504399307224962565 9718572282074870104680481)
          ·
            refine ⟨7288929211556152578510361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9718572282074870104680481 7288929211556152578510361)
            ·
              refine ⟨5466696908667114433882771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7288929211556152578510361 5466696908667114433882771)
              ·
                refine ⟨8200045363000671650824157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5466696908667114433882771 8200045363000671650824157)
                ·
                  refine ⟨3075017011125251869059059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8200045363000671650824157 3075017011125251869059059)
                  ·
                    refine ⟨4612525516687877803588589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3075017011125251869059059 4612525516687877803588589)
                    ·
                      refine ⟨1729697068757954176345721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612525516687877803588589 1729697068757954176345721)
                      ·
                        rfl

theorem cell23_3368573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 1, 3, 1, 3].length) (baseStart_3368573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368573 prefixEnd_3368573 := by exact prefixLift 3368573
  have htrace : WordTrace (prefixWord ++ tailWord_3368573) baseStart_3368573 baseEnd_3368573 := by
    simpa [prefixWord, tailWord_3368573, baseEnd_3368573] using wordTrace_append hprefix tailTrace_3368573
  have hstable : (prefixWord ++ tailWord_3368573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368573).length < 2 ^ (prefixWord ++ tailWord_3368573).sum := by decide
  have hdescent : baseEnd_3368573 < baseStart_3368573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368650 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_3368650 : Nat := 118140960795 + 3368650 * 2 ^ 59
def prefixEnd_3368650 : Nat := 4983230072969 + 3 ^ 40 * 3368650 * 2
def baseEnd_3368650 : Nat := 1729736606768350375082867

theorem tailTrace_3368650 : CollatzResearch.WordTrace tailWord_3368650 prefixEnd_3368650 1729736606768350375082867 := by
  unfold tailWord_3368650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30716189811490961115393851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81909839497309229641050269 30716189811490961115393851)
  ·
    refine ⟨46074284717236441673090777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30716189811490961115393851 46074284717236441673090777)
    ·
      refine ⟨34555713537927331254818083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46074284717236441673090777 34555713537927331254818083)
      ·
        refine ⟨51833570306890996882227125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34555713537927331254818083 51833570306890996882227125)
        ·
          refine ⟨4859397216271030957708793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51833570306890996882227125 4859397216271030957708793)
          ·
            refine ⟨3644547912203273218281595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4859397216271030957708793 3644547912203273218281595)
            ·
              refine ⟨5466821868304909827422393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644547912203273218281595 5466821868304909827422393)
              ·
                refine ⟨4100116401228682370566795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466821868304909827422393 4100116401228682370566795)
                ·
                  refine ⟨6150174601843023555850193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100116401228682370566795 6150174601843023555850193)
                  ·
                    refine ⟨4612630951382267666887645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6150174601843023555850193 4612630951382267666887645)
                    ·
                      refine ⟨1729736606768350375082867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612630951382267666887645 1729736606768350375082867)
                      ·
                        rfl

theorem cell23_3368650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_3368650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368650 prefixEnd_3368650 := by exact prefixLift 3368650
  have htrace : WordTrace (prefixWord ++ tailWord_3368650) baseStart_3368650 baseEnd_3368650 := by
    simpa [prefixWord, tailWord_3368650, baseEnd_3368650] using wordTrace_append hprefix tailTrace_3368650
  have hstable : (prefixWord ++ tailWord_3368650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368650).length < 2 ^ (prefixWord ++ tailWord_3368650).sum := by decide
  have hdescent : baseEnd_3368650 < baseStart_3368650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368680 : List Nat := [2, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_3368680 : Nat := 118140960795 + 3368680 * 2 ^ 59
def prefixEnd_3368680 : Nat := 4983230072969 + 3 ^ 40 * 3368680 * 2
def baseEnd_3368680 : Nat := 1729752011187985257707729

theorem tailTrace_3368680 : CollatzResearch.WordTrace tailWord_3368680 prefixEnd_3368680 1729752011187985257707729 := by
  unfold tailWord_3368680
  simp only [CollatzResearch.WordTrace]
  refine ⟨61432926717927579792583747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81910568957236773056778329 61432926717927579792583747)
  ·
    refine ⟨92149390076891369688875621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61432926717927579792583747 92149390076891369688875621)
    ·
      refine ⟨17278010639417131816664179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92149390076891369688875621 17278010639417131816664179)
      ·
        refine ⟨25917015959125697724996269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17278010639417131816664179 25917015959125697724996269)
        ·
          refine ⟨9718880984672136646873601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25917015959125697724996269 9718880984672136646873601)
          ·
            refine ⟨7289160738504102485155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9718880984672136646873601 7289160738504102485155201)
            ·
              refine ⟨5466870553878076863866401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289160738504102485155201 5466870553878076863866401)
              ·
                refine ⟨4100152915408557647899801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466870553878076863866401 4100152915408557647899801)
                ·
                  refine ⟨3075114686556418235924851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100152915408557647899801 3075114686556418235924851)
                  ·
                    refine ⟨4612672029834627353887277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3075114686556418235924851 4612672029834627353887277)
                    ·
                      refine ⟨1729752011187985257707729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612672029834627353887277 1729752011187985257707729)
                      ·
                        rfl

theorem cell23_3368680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_3368680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368680 prefixEnd_3368680 := by exact prefixLift 3368680
  have htrace : WordTrace (prefixWord ++ tailWord_3368680) baseStart_3368680 baseEnd_3368680 := by
    simpa [prefixWord, tailWord_3368680, baseEnd_3368680] using wordTrace_append hprefix tailTrace_3368680
  have hstable : (prefixWord ++ tailWord_3368680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368680).length < 2 ^ (prefixWord ++ tailWord_3368680).sum := by decide
  have hdescent : baseEnd_3368680 < baseStart_3368680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368736 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3]
def baseStart_3368736 : Nat := 118140960795 + 3368736 * 2 ^ 59
def prefixEnd_3368736 : Nat := 4983230072969 + 3 ^ 40 * 3368736 * 2
def baseEnd_3368736 : Nat := 1729780766104637038607471

theorem tailTrace_3368736 : CollatzResearch.WordTrace tailWord_3368736 prefixEnd_3368736 1729780766104637038607471 := by
  unfold tailWord_3368736
  simp only [CollatzResearch.WordTrace]
  refine ⟨61433947961826140574603031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81911930615768187432804041 61433947961826140574603031)
  ·
    refine ⟨92150921942739210861904547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61433947961826140574603031 92150921942739210861904547)
    ·
      refine ⟨138226382914108816292856821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92150921942739210861904547 138226382914108816292856821)
      ·
        refine ⟨12958723398197701527455327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138226382914108816292856821 12958723398197701527455327)
        ·
          refine ⟨19438085097296552291182991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12958723398197701527455327 19438085097296552291182991)
          ·
            refine ⟨29157127645944828436774487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19438085097296552291182991 29157127645944828436774487)
            ·
              refine ⟨43735691468917242655161731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29157127645944828436774487 43735691468917242655161731)
              ·
                refine ⟨65603537203375863982742597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43735691468917242655161731 65603537203375863982742597)
                ·
                  refine ⟨12300663225632974496764237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65603537203375863982742597 12300663225632974496764237)
                  ·
                    refine ⟨4612748709612365436286589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12300663225632974496764237 4612748709612365436286589)
                    ·
                      refine ⟨1729780766104637038607471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612748709612365436286589 1729780766104637038607471)
                      ·
                        rfl

theorem cell23_3368736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_3368736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368736 prefixEnd_3368736 := by exact prefixLift 3368736
  have htrace : WordTrace (prefixWord ++ tailWord_3368736) baseStart_3368736 baseEnd_3368736 := by
    simpa [prefixWord, tailWord_3368736, baseEnd_3368736] using wordTrace_append hprefix tailTrace_3368736
  have hstable : (prefixWord ++ tailWord_3368736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368736).length < 2 ^ (prefixWord ++ tailWord_3368736).sum := by decide
  have hdescent : baseEnd_3368736 < baseStart_3368736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368737 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 2, 2, 2]
def baseStart_3368737 : Nat := 118140960795 + 3368737 * 2 ^ 59
def prefixEnd_3368737 : Nat := 4983230072969 + 3 ^ 40 * 3368737 * 2
def baseEnd_3368737 : Nat := 1729781279585291534694967

theorem tailTrace_3368737 : CollatzResearch.WordTrace tailWord_3368737 prefixEnd_3368737 1729781279585291534694967 := by
  unfold tailWord_3368737
  simp only [CollatzResearch.WordTrace]
  refine ⟨122867932396648658319992465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81911954931099105546661643 122867932396648658319992465)
  ·
    refine ⟨92150949297486493739994349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122867932396648658319992465 92150949297486493739994349)
    ·
      refine ⟨34556605986557435152497881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92150949297486493739994349 34556605986557435152497881)
      ·
        refine ⟨25917454489918076364373411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34556605986557435152497881 25917454489918076364373411)
        ·
          refine ⟨38876181734877114546560117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25917454489918076364373411 38876181734877114546560117)
          ·
            refine ⟨3644642037644729488740011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38876181734877114546560117 3644642037644729488740011)
            ·
              refine ⟨5466963056467094233110017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3644642037644729488740011 5466963056467094233110017)
              ·
                refine ⟨4100222292350320674832513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5466963056467094233110017 4100222292350320674832513)
                ·
                  refine ⟨3075166719262740506124385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100222292350320674832513 3075166719262740506124385)
                  ·
                    refine ⟨2306375039447055379593289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075166719262740506124385 2306375039447055379593289)
                    ·
                      refine ⟨1729781279585291534694967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306375039447055379593289 1729781279585291534694967)
                      ·
                        rfl

theorem cell23_3368737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_3368737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368737 prefixEnd_3368737 := by exact prefixLift 3368737
  have htrace : WordTrace (prefixWord ++ tailWord_3368737) baseStart_3368737 baseEnd_3368737 := by
    simpa [prefixWord, tailWord_3368737, baseEnd_3368737] using wordTrace_append hprefix tailTrace_3368737
  have hstable : (prefixWord ++ tailWord_3368737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368737).length < 2 ^ (prefixWord ++ tailWord_3368737).sum := by decide
  have hdescent : baseEnd_3368737 < baseStart_3368737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368776 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_3368776 : Nat := 118140960795 + 3368776 * 2 ^ 59
def prefixEnd_3368776 : Nat := 4983230072969 + 3 ^ 40 * 3368776 * 2
def baseEnd_3368776 : Nat := 1729801305330816882107287

theorem tailTrace_3368776 : CollatzResearch.WordTrace tailWord_3368776 prefixEnd_3368776 1729801305330816882107287 := by
  unfold tailWord_3368776
  simp only [CollatzResearch.WordTrace]
  refine ⟨61434677421753683990331091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81912903229004911987108121 61434677421753683990331091)
  ·
    refine ⟨92152016132630525985496637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61434677421753683990331091 92152016132630525985496637)
    ·
      refine ⟨34557006049736447244561239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92152016132630525985496637 34557006049736447244561239)
      ·
        refine ⟨51835509074604670866841859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34557006049736447244561239 51835509074604670866841859)
        ·
          refine ⟨77753263611907006300262789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51835509074604670866841859 77753263611907006300262789)
          ·
            refine ⟨14578736927232563681299273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77753263611907006300262789 14578736927232563681299273)
            ·
              refine ⟨10934052695424422760974455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14578736927232563681299273 10934052695424422760974455)
              ·
                refine ⟨16401079043136634141461683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10934052695424422760974455 16401079043136634141461683)
                ·
                  refine ⟨24601618564704951212192525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16401079043136634141461683 24601618564704951212192525)
                  ·
                    refine ⟨9225606961764356704572197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24601618564704951212192525 9225606961764356704572197)
                    ·
                      refine ⟨1729801305330816882107287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9225606961764356704572197 1729801305330816882107287)
                      ·
                        rfl

theorem cell23_3368776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_3368776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368776 prefixEnd_3368776 := by exact prefixLift 3368776
  have htrace : WordTrace (prefixWord ++ tailWord_3368776) baseStart_3368776 baseEnd_3368776 := by
    simpa [prefixWord, tailWord_3368776, baseEnd_3368776] using wordTrace_append hprefix tailTrace_3368776
  have hstable : (prefixWord ++ tailWord_3368776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368776).length < 2 ^ (prefixWord ++ tailWord_3368776).sum := by decide
  have hdescent : baseEnd_3368776 < baseStart_3368776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368826 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_3368826 : Nat := 118140960795 + 3368826 * 2 ^ 59
def prefixEnd_3368826 : Nat := 4983230072969 + 3 ^ 40 * 3368826 * 2
def baseEnd_3368826 : Nat := 1729826979363541686482057

theorem tailTrace_3368826 : CollatzResearch.WordTrace tailWord_3368826 prefixEnd_3368826 1729826979363541686482057 := by
  unfold tailWord_3368826
  simp only [CollatzResearch.WordTrace]
  refine ⟨30717794623331556629995583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81914118995550817679988221 30717794623331556629995583)
  ·
    refine ⟨46076691934997334944993375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30717794623331556629995583 46076691934997334944993375)
    ·
      refine ⟨69115037902496002417490063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46076691934997334944993375 69115037902496002417490063)
      ·
        refine ⟨103672556853744003626235095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69115037902496002417490063 103672556853744003626235095)
        ·
          refine ⟨155508835280616005439352643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103672556853744003626235095 155508835280616005439352643)
          ·
            refine ⟨233263252920924008159028965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155508835280616005439352643 233263252920924008159028965)
            ·
              refine ⟨43736859922673251529817931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233263252920924008159028965 43736859922673251529817931)
              ·
                refine ⟨65605289884009877294726897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43736859922673251529817931 65605289884009877294726897)
                ·
                  refine ⟨49203967413007407971045173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65605289884009877294726897 49203967413007407971045173)
                  ·
                    refine ⟨4612871944969444497285485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49203967413007407971045173 4612871944969444497285485)
                    ·
                      refine ⟨1729826979363541686482057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612871944969444497285485 1729826979363541686482057)
                      ·
                        rfl

theorem cell23_3368826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_3368826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368826 prefixEnd_3368826 := by exact prefixLift 3368826
  have htrace : WordTrace (prefixWord ++ tailWord_3368826) baseStart_3368826 baseEnd_3368826 := by
    simpa [prefixWord, tailWord_3368826, baseEnd_3368826] using wordTrace_append hprefix tailTrace_3368826
  have hstable : (prefixWord ++ tailWord_3368826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368826).length < 2 ^ (prefixWord ++ tailWord_3368826).sum := by decide
  have hdescent : baseEnd_3368826 < baseStart_3368826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368850 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 6]
def baseStart_3368850 : Nat := 118140960795 + 3368850 * 2 ^ 59
def prefixEnd_3368850 : Nat := 4983230072969 + 3 ^ 40 * 3368850 * 2
def baseEnd_3368850 : Nat := 192204366988805510286883

theorem tailTrace_3368850 : CollatzResearch.WordTrace tailWord_3368850 prefixEnd_3368850 192204366988805510286883 := by
  unfold tailWord_3368850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30718013461309819654714001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81914702563492852412570669 30718013461309819654714001)
  ·
    refine ⟨23038510095982364741035501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30718013461309819654714001 23038510095982364741035501)
    ·
      refine ⟨8639441285993386777888313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23038510095982364741035501 8639441285993386777888313)
      ·
        refine ⟨6479580964495040083416235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8639441285993386777888313 6479580964495040083416235)
        ·
          refine ⟨9719371446742560125124353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6479580964495040083416235 9719371446742560125124353)
          ·
            refine ⟨7289528585056920093843265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719371446742560125124353 7289528585056920093843265)
            ·
              refine ⟨5467146438792690070382449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289528585056920093843265 5467146438792690070382449)
              ·
                refine ⟨4100359829094517552786837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467146438792690070382449 4100359829094517552786837)
                ·
                  refine ⟨192204366988805510286883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4100359829094517552786837 192204366988805510286883)
                  ·
                    rfl

theorem cell23_3368850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_3368850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368850 prefixEnd_3368850 := by exact prefixLift 3368850
  have htrace : WordTrace (prefixWord ++ tailWord_3368850) baseStart_3368850 baseEnd_3368850 := by
    simpa [prefixWord, tailWord_3368850, baseEnd_3368850] using wordTrace_append hprefix tailTrace_3368850
  have hstable : (prefixWord ++ tailWord_3368850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368850).length < 2 ^ (prefixWord ++ tailWord_3368850).sum := by decide
  have hdescent : baseEnd_3368850 < baseStart_3368850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368883 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 4]
def baseStart_3368883 : Nat := 118140960795 + 3368883 * 2 ^ 59
def prefixEnd_3368883 : Nat := 4983230072969 + 3 ^ 40 * 3368883 * 2
def baseEnd_3368883 : Nat := 1729856247760847963469295

theorem tailTrace_3368883 : CollatzResearch.WordTrace tailWord_3368883 prefixEnd_3368883 1729856247760847963469295 := by
  unfold tailWord_3368883
  simp only [CollatzResearch.WordTrace]
  refine ⟨122873257454119725254807303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81915504969413150169871535 122873257454119725254807303)
  ·
    refine ⟨184309886181179587882210955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122873257454119725254807303 184309886181179587882210955)
    ·
      refine ⟨276464829271769381823316433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184309886181179587882210955 276464829271769381823316433)
      ·
        refine ⟨207348621953827036367487325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276464829271769381823316433 207348621953827036367487325)
        ·
          refine ⟨77755733232685138637807747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207348621953827036367487325 77755733232685138637807747)
          ·
            refine ⟨116633599849027707956711621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77755733232685138637807747 116633599849027707956711621)
            ·
              refine ⟨21868799971692695241883429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116633599849027707956711621 21868799971692695241883429)
              ·
                refine ⟨4100399994692380357853143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21868799971692695241883429 4100399994692380357853143)
                ·
                  refine ⟨6150599992038570536779715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4100399994692380357853143 6150599992038570536779715)
                  ·
                    refine ⟨9225899988057855805169573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6150599992038570536779715 9225899988057855805169573)
                    ·
                      refine ⟨1729856247760847963469295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9225899988057855805169573 1729856247760847963469295)
                      ·
                        rfl

theorem cell23_3368883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_3368883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368883 prefixEnd_3368883 := by exact prefixLift 3368883
  have htrace : WordTrace (prefixWord ++ tailWord_3368883) baseStart_3368883 baseEnd_3368883 := by
    simpa [prefixWord, tailWord_3368883, baseEnd_3368883] using wordTrace_append hprefix tailTrace_3368883
  have hstable : (prefixWord ++ tailWord_3368883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368883).length < 2 ^ (prefixWord ++ tailWord_3368883).sum := by decide
  have hdescent : baseEnd_3368883 < baseStart_3368883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368893 : List Nat := [1, 4, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_3368893 : Nat := 118140960795 + 3368893 * 2 ^ 59
def prefixEnd_3368893 : Nat := 4983230072969 + 3 ^ 40 * 3368893 * 2
def baseEnd_3368893 : Nat := 576620460855797641448083

theorem tailTrace_3368893 : CollatzResearch.WordTrace tailWord_3368893 prefixEnd_3368893 576620460855797641448083 := by
  unfold tailWord_3368893
  simp only [CollatzResearch.WordTrace]
  refine ⟨122873622184083496962671333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81915748122722331308447555 122873622184083496962671333)
  ·
    refine ⟨23038804159515655680500875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122873622184083496962671333 23038804159515655680500875)
    ·
      refine ⟨34558206239273483520751313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23038804159515655680500875 34558206239273483520751313)
      ·
        refine ⟨25918654679455112640563485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34558206239273483520751313 25918654679455112640563485)
        ·
          refine ⟨9719495504795667240211307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25918654679455112640563485 9719495504795667240211307)
          ·
            refine ⟨14579243257193500860316961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719495504795667240211307 14579243257193500860316961)
            ·
              refine ⟨10934432442895125645237721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14579243257193500860316961 10934432442895125645237721)
              ·
                refine ⟨8200824332171344233928291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10934432442895125645237721 8200824332171344233928291)
                ·
                  refine ⟨12301236498257016350892437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8200824332171344233928291 12301236498257016350892437)
                  ·
                    refine ⟨576620460855797641448083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12301236498257016350892437 576620460855797641448083)
                    ·
                      rfl

theorem cell23_3368893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_3368893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368893 prefixEnd_3368893 := by exact prefixLift 3368893
  have htrace : WordTrace (prefixWord ++ tailWord_3368893) baseStart_3368893 baseEnd_3368893 := by
    simpa [prefixWord, tailWord_3368893, baseEnd_3368893] using wordTrace_append hprefix tailTrace_3368893
  have hstable : (prefixWord ++ tailWord_3368893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368893).length < 2 ^ (prefixWord ++ tailWord_3368893).sum := by decide
  have hdescent : baseEnd_3368893 < baseStart_3368893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368894 : List Nat := [4, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3]
def baseStart_3368894 : Nat := 118140960795 + 3368894 * 2 ^ 59
def prefixEnd_3368894 : Nat := 4983230072969 + 3 ^ 40 * 3368894 * 2
def baseEnd_3368894 : Nat := 1729861896048047420431745

theorem tailTrace_3368894 : CollatzResearch.WordTrace tailWord_3368894 prefixEnd_3368894 1729861896048047420431745 := by
  unfold tailWord_3368894
  simp only [CollatzResearch.WordTrace]
  refine ⟨15359207332134984266682217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81915772438053249422305157 15359207332134984266682217)
  ·
    refine ⟨11519405499101238200011663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15359207332134984266682217 11519405499101238200011663)
    ·
      refine ⟨17279108248651857300017495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11519405499101238200011663 17279108248651857300017495)
      ·
        refine ⟨25918662372977785950026243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17279108248651857300017495 25918662372977785950026243)
        ·
          refine ⟨38877993559466678925039365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25918662372977785950026243 38877993559466678925039365)
          ·
            refine ⟨7289623792400002298444881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38877993559466678925039365 7289623792400002298444881)
            ·
              refine ⟨5467217844300001723833661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289623792400002298444881 5467217844300001723833661)
              ·
                refine ⟨2050206691612500646437623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5467217844300001723833661 2050206691612500646437623)
                ·
                  refine ⟨3075310037418750969656435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050206691612500646437623 3075310037418750969656435)
                  ·
                    refine ⟨4612965056128126454484653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3075310037418750969656435 4612965056128126454484653)
                    ·
                      refine ⟨1729861896048047420431745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4612965056128126454484653 1729861896048047420431745)
                      ·
                        rfl

theorem cell23_3368894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_3368894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368894 prefixEnd_3368894 := by exact prefixLift 3368894
  have htrace : WordTrace (prefixWord ++ tailWord_3368894) baseStart_3368894 baseEnd_3368894 := by
    simpa [prefixWord, tailWord_3368894, baseEnd_3368894] using wordTrace_append hprefix tailTrace_3368894
  have hstable : (prefixWord ++ tailWord_3368894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368894).length < 2 ^ (prefixWord ++ tailWord_3368894).sum := by decide
  have hdescent : baseEnd_3368894 < baseStart_3368894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368917 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 3, 2, 2]
def baseStart_3368917 : Nat := 118140960795 + 3368917 * 2 ^ 59
def prefixEnd_3368917 : Nat := 4983230072969 + 3 ^ 40 * 3368917 * 2
def baseEnd_3368917 : Nat := 1729873706103100830444139

theorem tailTrace_3368917 : CollatzResearch.WordTrace tailWord_3368917 prefixEnd_3368917 1729873706103100830444139 := by
  unfold tailWord_3368917
  simp only [CollatzResearch.WordTrace]
  refine ⟨122874497535996549061545005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81916331690664366041030003 122874497535996549061545005)
  ·
    refine ⟨46077936575998705898079377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122874497535996549061545005 46077936575998705898079377)
    ·
      refine ⟨34558452431999029423559533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46077936575998705898079377 34558452431999029423559533)
      ·
        refine ⟨12959419661999636033834825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34558452431999029423559533 12959419661999636033834825)
        ·
          refine ⟨9719564746499727025376119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12959419661999636033834825 9719564746499727025376119)
          ·
            refine ⟨14579347119749590538064179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9719564746499727025376119 14579347119749590538064179)
            ·
              refine ⟨21869020679624385807096269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14579347119749590538064179 21869020679624385807096269)
              ·
                refine ⟨8200882754859144677661101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21869020679624385807096269 8200882754859144677661101)
                ·
                  refine ⟨3075331033072179254122913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8200882754859144677661101 3075331033072179254122913)
                  ·
                    refine ⟨2306498274804134440592185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075331033072179254122913 2306498274804134440592185)
                    ·
                      refine ⟨1729873706103100830444139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306498274804134440592185 1729873706103100830444139)
                      ·
                        rfl

theorem cell23_3368917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_3368917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368917 prefixEnd_3368917 := by exact prefixLift 3368917
  have htrace : WordTrace (prefixWord ++ tailWord_3368917) baseStart_3368917 baseEnd_3368917 := by
    simpa [prefixWord, tailWord_3368917, baseEnd_3368917] using wordTrace_append hprefix tailTrace_3368917
  have hstable : (prefixWord ++ tailWord_3368917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368917).length < 2 ^ (prefixWord ++ tailWord_3368917).sum := by decide
  have hdescent : baseEnd_3368917 < baseStart_3368917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3368927 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 2, 4]
def baseStart_3368927 : Nat := 118140960795 + 3368927 * 2 ^ 59
def prefixEnd_3368927 : Nat := 4983230072969 + 3 ^ 40 * 3368927 * 2
def baseEnd_3368927 : Nat := 576626280303215263773031

theorem tailTrace_3368927 : CollatzResearch.WordTrace tailWord_3368927 prefixEnd_3368927 576626280303215263773031 := by
  unfold tailWord_3368927
  simp only [CollatzResearch.WordTrace]
  refine ⟨122874862265960320769409035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81916574843973547179606023 122874862265960320769409035)
  ·
    refine ⟨184312293398940481154113553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122874862265960320769409035 184312293398940481154113553)
    ·
      refine ⟨138234220049205360865585165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184312293398940481154113553 138234220049205360865585165)
      ·
        refine ⟨51837832518452010324594437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138234220049205360865585165 51837832518452010324594437)
        ·
          refine ⟨9719593597209751935861457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51837832518452010324594437 9719593597209751935861457)
          ·
            refine ⟨7289695197907313951896093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9719593597209751935861457 7289695197907313951896093)
            ·
              refine ⟨2733635699215242731961035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7289695197907313951896093 2733635699215242731961035)
              ·
                refine ⟨4100453548822864097941553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733635699215242731961035 4100453548822864097941553)
                ·
                  refine ⟨3075340161617148073456165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100453548822864097941553 3075340161617148073456165)
                  ·
                    refine ⟨576626280303215263773031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075340161617148073456165 576626280303215263773031)
                    ·
                      rfl

theorem cell23_3368927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 2, 4].length) (baseStart_3368927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3368927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3368927 prefixEnd_3368927 := by exact prefixLift 3368927
  have htrace : WordTrace (prefixWord ++ tailWord_3368927) baseStart_3368927 baseEnd_3368927 := by
    simpa [prefixWord, tailWord_3368927, baseEnd_3368927] using wordTrace_append hprefix tailTrace_3368927
  have hstable : (prefixWord ++ tailWord_3368927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3368927).length < 2 ^ (prefixWord ++ tailWord_3368927).sum := by decide
  have hdescent : baseEnd_3368927 < baseStart_3368927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3368927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369024 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2]
def baseStart_3369024 : Nat := 118140960795 + 3369024 * 2 ^ 59
def prefixEnd_3369024 : Nat := 4983230072969 + 3 ^ 40 * 3369024 * 2
def baseEnd_3369024 : Nat := 1729928648533131911806147

theorem tailTrace_3369024 : CollatzResearch.WordTrace tailWord_3369024 prefixEnd_3369024 1729928648533131911806147 := by
  unfold tailWord_3369024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61439200073304453167845063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81918933431072604223793417 61439200073304453167845063)
  ·
    refine ⟨92158800109956679751767595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61439200073304453167845063 92158800109956679751767595)
    ·
      refine ⟨138238200164935019627651393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92158800109956679751767595 138238200164935019627651393)
      ·
        refine ⟨103678650123701264720738545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138238200164935019627651393 103678650123701264720738545)
        ·
          refine ⟨77758987592775948540553909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103678650123701264720738545 77758987592775948540553909)
          ·
            refine ⟨7289905086822745175676929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77758987592775948540553909 7289905086822745175676929)
            ·
              refine ⟨5467428815117058881757697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7289905086822745175676929 5467428815117058881757697)
              ·
                refine ⟨4100571611337794161318273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5467428815117058881757697 4100571611337794161318273)
                ·
                  refine ⟨3075428708503345620988705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100571611337794161318273 3075428708503345620988705)
                  ·
                    refine ⟨2306571531377509215741529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075428708503345620988705 2306571531377509215741529)
                    ·
                      refine ⟨1729928648533131911806147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306571531377509215741529 1729928648533131911806147)
                      ·
                        rfl

theorem cell23_3369024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_3369024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369024 prefixEnd_3369024 := by exact prefixLift 3369024
  have htrace : WordTrace (prefixWord ++ tailWord_3369024) baseStart_3369024 baseEnd_3369024 := by
    simpa [prefixWord, tailWord_3369024, baseEnd_3369024] using wordTrace_append hprefix tailTrace_3369024
  have hstable : (prefixWord ++ tailWord_3369024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369024).length < 2 ^ (prefixWord ++ tailWord_3369024).sum := by decide
  have hdescent : baseEnd_3369024 < baseStart_3369024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369050 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2]
def baseStart_3369050 : Nat := 118140960795 + 3369050 * 2 ^ 59
def prefixEnd_3369050 : Nat := 4983230072969 + 3 ^ 40 * 3369050 * 2
def baseEnd_3369050 : Nat := 1729941999030148810081027

theorem tailTrace_3369050 : CollatzResearch.WordTrace tailWord_3369050 prefixEnd_3369050 1729941999030148810081027 := by
  unfold tailWord_3369050
  simp only [CollatzResearch.WordTrace]
  refine ⟨30719837111128678194034151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81919565629676475184091069 30719837111128678194034151)
  ·
    refine ⟨46079755666693017291051227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30719837111128678194034151 46079755666693017291051227)
    ·
      refine ⟨69119633500039525936576841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46079755666693017291051227 69119633500039525936576841)
      ·
        refine ⟨51839725125029644452432631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69119633500039525936576841 51839725125029644452432631)
        ·
          refine ⟨77759587687544466678648947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51839725125029644452432631 77759587687544466678648947)
          ·
            refine ⟨116639381531316700017973421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77759587687544466678648947 116639381531316700017973421)
            ·
              refine ⟨43739768074243762506740033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116639381531316700017973421 43739768074243762506740033)
              ·
                refine ⟨32804826055682821880055025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43739768074243762506740033 32804826055682821880055025)
                ·
                  refine ⟨24603619541762116410041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32804826055682821880055025 24603619541762116410041269)
                  ·
                    refine ⟨2306589332040198413441369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24603619541762116410041269 2306589332040198413441369)
                    ·
                      refine ⟨1729941999030148810081027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306589332040198413441369 1729941999030148810081027)
                      ·
                        rfl

theorem cell23_3369050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_3369050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369050 prefixEnd_3369050 := by exact prefixLift 3369050
  have htrace : WordTrace (prefixWord ++ tailWord_3369050) baseStart_3369050 baseEnd_3369050 := by
    simpa [prefixWord, tailWord_3369050, baseEnd_3369050] using wordTrace_append hprefix tailTrace_3369050
  have hstable : (prefixWord ++ tailWord_3369050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369050).length < 2 ^ (prefixWord ++ tailWord_3369050).sum := by decide
  have hdescent : baseEnd_3369050 < baseStart_3369050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369060 : List Nat := [2, 3, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_3369060 : Nat := 118140960795 + 3369060 * 2 ^ 59
def prefixEnd_3369060 : Nat := 4983230072969 + 3 ^ 40 * 3369060 * 2
def baseEnd_3369060 : Nat := 576649044612231256985327

theorem tailTrace_3369060 : CollatzResearch.WordTrace tailWord_3369060 prefixEnd_3369060 576649044612231256985327 := by
  unfold tailWord_3369060
  simp only [CollatzResearch.WordTrace]
  refine ⟨61439856587239242242000317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81919808782985656322667089 61439856587239242242000317)
  ·
    refine ⟨23039946220214715840750119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61439856587239242242000317 23039946220214715840750119)
    ·
      refine ⟨34559919330322073761125179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23039946220214715840750119 34559919330322073761125179)
      ·
        refine ⟨51839878995483110641687769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34559919330322073761125179 51839878995483110641687769)
        ·
          refine ⟨38879909246612332981265827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51839878995483110641687769 38879909246612332981265827)
          ·
            refine ⟨58319863869918499471898741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38879909246612332981265827 58319863869918499471898741)
            ·
              refine ⟨5467487237804859325490507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58319863869918499471898741 5467487237804859325490507)
              ·
                refine ⟨8201230856707288988235761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467487237804859325490507 8201230856707288988235761)
                ·
                  refine ⟨6150923142530466741176821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8201230856707288988235761 6150923142530466741176821)
                  ·
                    refine ⟨576649044612231256985327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6150923142530466741176821 576649044612231256985327)
                    ·
                      rfl

theorem cell23_3369060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_3369060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369060 prefixEnd_3369060 := by exact prefixLift 3369060
  have htrace : WordTrace (prefixWord ++ tailWord_3369060) baseStart_3369060 baseEnd_3369060 := by
    simpa [prefixWord, tailWord_3369060, baseEnd_3369060] using wordTrace_append hprefix tailTrace_3369060
  have hstable : (prefixWord ++ tailWord_3369060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369060).length < 2 ^ (prefixWord ++ tailWord_3369060).sum := by decide
  have hdescent : baseEnd_3369060 < baseStart_3369060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369141 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3369141 : Nat := 118140960795 + 3369141 * 2 ^ 59
def prefixEnd_3369141 : Nat := 4983230072969 + 3 ^ 40 * 3369141 * 2
def baseEnd_3369141 : Nat := 576662908589902651347703

theorem tailTrace_3369141 : CollatzResearch.WordTrace tailWord_3369141 prefixEnd_3369141 576662908589902651347703 := by
  unfold tailWord_3369141
  simp only [CollatzResearch.WordTrace]
  refine ⟨122882667487185035317699277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81921778324790023545132851 122882667487185035317699277)
  ·
    refine ⟨46081000307694388244137229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122882667487185035317699277 46081000307694388244137229)
    ·
      refine ⟨17280375115385395591551461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46081000307694388244137229 17280375115385395591551461)
      ·
        refine ⟨3240070334134761673415899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17280375115385395591551461 3240070334134761673415899)
        ·
          refine ⟨4860105501202142510123849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240070334134761673415899 4860105501202142510123849)
          ·
            refine ⟨3645079125901606882592887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4860105501202142510123849 3645079125901606882592887)
            ·
              refine ⟨5467618688852410323889331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645079125901606882592887 5467618688852410323889331)
              ·
                refine ⟨8201428033278615485833997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467618688852410323889331 8201428033278615485833997)
                ·
                  refine ⟨3075535512479480807187749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8201428033278615485833997 3075535512479480807187749)
                  ·
                    refine ⟨576662908589902651347703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075535512479480807187749 576662908589902651347703)
                    ·
                      rfl

theorem cell23_3369141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3369141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369141 prefixEnd_3369141 := by exact prefixLift 3369141
  have htrace : WordTrace (prefixWord ++ tailWord_3369141) baseStart_3369141 baseEnd_3369141 := by
    simpa [prefixWord, tailWord_3369141, baseEnd_3369141] using wordTrace_append hprefix tailTrace_3369141
  have hstable : (prefixWord ++ tailWord_3369141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369141).length < 2 ^ (prefixWord ++ tailWord_3369141).sum := by decide
  have hdescent : baseEnd_3369141 < baseStart_3369141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369210 : List Nat := [3, 1, 1, 1, 1, 5, 3, 8]
def baseStart_3369210 : Nat := 118140960795 + 3369210 * 2 ^ 59
def prefixEnd_3369210 : Nat := 4983230072969 + 3 ^ 40 * 3369210 * 2
def baseEnd_3369210 : Nat := 64074968738328451262233

theorem tailTrace_3369210 : CollatzResearch.WordTrace tailWord_3369210 prefixEnd_3369210 64074968738328451262233 := by
  unfold tailWord_3369210
  simp only [CollatzResearch.WordTrace]
  refine ⟨30721296030983765025490271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81923456082623373401307389 30721296030983765025490271)
  ·
    refine ⟨46081944046475647538235407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30721296030983765025490271 46081944046475647538235407)
    ·
      refine ⟨69122916069713471307353111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46081944046475647538235407 69122916069713471307353111)
      ·
        refine ⟨103684374104570206961029667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69122916069713471307353111 103684374104570206961029667)
        ·
          refine ⟨155526561156855310441544501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103684374104570206961029667 155526561156855310441544501)
          ·
            refine ⟨14580615108455185353894797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155526561156855310441544501 14580615108455185353894797)
            ·
              refine ⟨5467730665670694507710549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14580615108455185353894797 5467730665670694507710549)
              ·
                refine ⟨64074968738328451262233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5467730665670694507710549 64074968738328451262233)
                ·
                  rfl

theorem cell23_3369210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 3, 8].length) (baseStart_3369210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369210 prefixEnd_3369210 := by exact prefixLift 3369210
  have htrace : WordTrace (prefixWord ++ tailWord_3369210) baseStart_3369210 baseEnd_3369210 := by
    simpa [prefixWord, tailWord_3369210, baseEnd_3369210] using wordTrace_append hprefix tailTrace_3369210
  have hstable : (prefixWord ++ tailWord_3369210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369210).length < 2 ^ (prefixWord ++ tailWord_3369210).sum := by decide
  have hdescent : baseEnd_3369210 < baseStart_3369210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369214 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 2, 4]
def baseStart_3369214 : Nat := 118140960795 + 3369214 * 2 ^ 59
def prefixEnd_3369214 : Nat := 4983230072969 + 3 ^ 40 * 3369214 * 2
def baseEnd_3369214 : Nat := 576675403285828722810091

theorem tailTrace_3369214 : CollatzResearch.WordTrace tailWord_3369214 prefixEnd_3369214 576675403285828722810091 := by
  unfold tailWord_3369214
  simp only [CollatzResearch.WordTrace]
  refine ⟨15360666251990071098138337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81923553343947045856737797 15360666251990071098138337)
  ·
    refine ⟨11520499688992553323603753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15360666251990071098138337 11520499688992553323603753)
    ·
      refine ⟨8640374766744414992702815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11520499688992553323603753 8640374766744414992702815)
      ·
        refine ⟨12960562150116622489054223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8640374766744414992702815 12960562150116622489054223)
        ·
          refine ⟨19440843225174933733581335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12960562150116622489054223 19440843225174933733581335)
          ·
            refine ⟨29161264837762400600372003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19440843225174933733581335 29161264837762400600372003)
            ·
              refine ⟨43741897256643600900558005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29161264837762400600372003 43741897256643600900558005)
              ·
                refine ⟨4100802867810337584427313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43741897256643600900558005 4100802867810337584427313)
                ·
                  refine ⟨3075602150857753188320485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100802867810337584427313 3075602150857753188320485)
                  ·
                    refine ⟨576675403285828722810091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075602150857753188320485 576675403285828722810091)
                    ·
                      rfl

theorem cell23_3369214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_3369214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369214 prefixEnd_3369214 := by exact prefixLift 3369214
  have htrace : WordTrace (prefixWord ++ tailWord_3369214) baseStart_3369214 baseEnd_3369214 := by
    simpa [prefixWord, tailWord_3369214, baseEnd_3369214] using wordTrace_append hprefix tailTrace_3369214
  have hstable : (prefixWord ++ tailWord_3369214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369214).length < 2 ^ (prefixWord ++ tailWord_3369214).sum := by decide
  have hdescent : baseEnd_3369214 < baseStart_3369214 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369217 : List Nat := [1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 4]
def baseStart_3369217 : Nat := 118140960795 + 3369217 * 2 ^ 59
def prefixEnd_3369217 : Nat := 4983230072969 + 3 ^ 40 * 3369217 * 2
def baseEnd_3369217 : Nat := 1730027750299449656692759

theorem tailTrace_3369217 : CollatzResearch.WordTrace tailWord_3369217 prefixEnd_3369217 1730027750299449656692759 := by
  unfold tailWord_3369217
  simp only [CollatzResearch.WordTrace]
  refine ⟨122885439434909700297465905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81923626289939800198310603 122885439434909700297465905)
  ·
    refine ⟨92164079576182275223099429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122885439434909700297465905 92164079576182275223099429)
    ·
      refine ⟨17280764920534176604331143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92164079576182275223099429 17280764920534176604331143)
      ·
        refine ⟨25921147380801264906496715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17280764920534176604331143 25921147380801264906496715)
        ·
          refine ⟨38881721071201897359745073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25921147380801264906496715 38881721071201897359745073)
          ·
            refine ⟨29161290803401423019808805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38881721071201897359745073 29161290803401423019808805)
            ·
              refine ⟨5467742025637766816214151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29161290803401423019808805 5467742025637766816214151)
              ·
                refine ⟨8201613038456650224321227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467742025637766816214151 8201613038456650224321227)
                ·
                  refine ⟨12302419557684975336481841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8201613038456650224321227 12302419557684975336481841)
                  ·
                    refine ⟨9226814668263731502361381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12302419557684975336481841 9226814668263731502361381)
                    ·
                      refine ⟨1730027750299449656692759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9226814668263731502361381 1730027750299449656692759)
                      ·
                        rfl

theorem cell23_3369217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_3369217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369217 prefixEnd_3369217 := by exact prefixLift 3369217
  have htrace : WordTrace (prefixWord ++ tailWord_3369217) baseStart_3369217 baseEnd_3369217 := by
    simpa [prefixWord, tailWord_3369217, baseEnd_3369217] using wordTrace_append hprefix tailTrace_3369217
  have hstable : (prefixWord ++ tailWord_3369217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369217).length < 2 ^ (prefixWord ++ tailWord_3369217).sum := by decide
  have hdescent : baseEnd_3369217 < baseStart_3369217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369237 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 3]
def baseStart_3369237 : Nat := 118140960795 + 3369237 * 2 ^ 59
def prefixEnd_3369237 : Nat := 4983230072969 + 3 ^ 40 * 3369237 * 2
def baseEnd_3369237 : Nat := 1730038019912539578442667

theorem tailTrace_3369237 : CollatzResearch.WordTrace tailWord_3369237 prefixEnd_3369237 1730038019912539578442667 := by
  unfold tailWord_3369237
  simp only [CollatzResearch.WordTrace]
  refine ⟨122886168894837243713193965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81924112596558162475462643 122886168894837243713193965)
  ·
    refine ⟨46082313335563966392447737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122886168894837243713193965 46082313335563966392447737)
    ·
      refine ⟨34561735001672974794335803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46082313335563966392447737 34561735001672974794335803)
      ·
        refine ⟨51842602502509462191503705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34561735001672974794335803 51842602502509462191503705)
        ·
          refine ⟨38881951876882096643627779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51842602502509462191503705 38881951876882096643627779)
          ·
            refine ⟨58322927815323144965441669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38881951876882096643627779 58322927815323144965441669)
            ·
              refine ⟨10935548965373089681020313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58322927815323144965441669 10935548965373089681020313)
              ·
                refine ⟨8201661724029817260765235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10935548965373089681020313 8201661724029817260765235)
                ·
                  refine ⟨12302492586044725891147853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8201661724029817260765235 12302492586044725891147853)
                  ·
                    refine ⟨4613434719766772209180445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12302492586044725891147853 4613434719766772209180445)
                    ·
                      refine ⟨1730038019912539578442667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4613434719766772209180445 1730038019912539578442667)
                      ·
                        rfl

theorem cell23_3369237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_3369237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369237 prefixEnd_3369237 := by exact prefixLift 3369237
  have htrace : WordTrace (prefixWord ++ tailWord_3369237) baseStart_3369237 baseEnd_3369237 := by
    simpa [prefixWord, tailWord_3369237, baseEnd_3369237] using wordTrace_append hprefix tailTrace_3369237
  have hstable : (prefixWord ++ tailWord_3369237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369237).length < 2 ^ (prefixWord ++ tailWord_3369237).sum := by decide
  have hdescent : baseEnd_3369237 < baseStart_3369237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369260 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_3369260 : Nat := 118140960795 + 3369260 * 2 ^ 59
def prefixEnd_3369260 : Nat := 4983230072969 + 3 ^ 40 * 3369260 * 2
def baseEnd_3369260 : Nat := 1730049829967592988455061

theorem tailTrace_3369260 : CollatzResearch.WordTrace tailWord_3369260 prefixEnd_3369260 1730049829967592988455061 := by
  unfold tailWord_3369260
  simp only [CollatzResearch.WordTrace]
  refine ⟨61443503886876959320640617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81924671849169279094187489 61443503886876959320640617)
  ·
    refine ⟨46082627915157719490480463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61443503886876959320640617 46082627915157719490480463)
    ·
      refine ⟨69123941872736579235720695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46082627915157719490480463 69123941872736579235720695)
      ·
        refine ⟨103685912809104868853581043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69123941872736579235720695 103685912809104868853581043)
        ·
          refine ⟨155528869213657303280371565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103685912809104868853581043 155528869213657303280371565)
          ·
            refine ⟨58323325955121488730139337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155528869213657303280371565 58323325955121488730139337)
            ·
              refine ⟨43742494466341116547604503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58323325955121488730139337 43742494466341116547604503)
              ·
                refine ⟨65613741699511674821406755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43742494466341116547604503 65613741699511674821406755)
                ·
                  refine ⟨98420612549267512232110133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65613741699511674821406755 98420612549267512232110133)
                  ·
                    refine ⟨9226932426493829271760325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98420612549267512232110133 9226932426493829271760325)
                    ·
                      refine ⟨1730049829967592988455061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9226932426493829271760325 1730049829967592988455061)
                      ·
                        rfl

theorem cell23_3369260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_3369260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369260 prefixEnd_3369260 := by exact prefixLift 3369260
  have htrace : WordTrace (prefixWord ++ tailWord_3369260) baseStart_3369260 baseEnd_3369260 := by
    simpa [prefixWord, tailWord_3369260, baseEnd_3369260] using wordTrace_append hprefix tailTrace_3369260
  have hstable : (prefixWord ++ tailWord_3369260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369260).length < 2 ^ (prefixWord ++ tailWord_3369260).sum := by decide
  have hdescent : baseEnd_3369260 < baseStart_3369260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369297 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 5]
def baseStart_3369297 : Nat := 118140960795 + 3369297 * 2 ^ 59
def prefixEnd_3369297 : Nat := 4983230072969 + 3 ^ 40 * 3369297 * 2
def baseEnd_3369297 : Nat := 1730068828751809343692391

theorem tailTrace_3369297 : CollatzResearch.WordTrace tailWord_3369297 prefixEnd_3369297 1730068828751809343692391 := by
  unfold tailWord_3369297
  simp only [CollatzResearch.WordTrace]
  refine ⟨122888357274619873960378145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81925571516413249306918763 122888357274619873960378145)
  ·
    refine ⟨92166267955964905470283609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122888357274619873960378145 92166267955964905470283609)
    ·
      refine ⟨69124700966973679102712707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92166267955964905470283609 69124700966973679102712707)
      ·
        refine ⟨103687051450460518654069061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69124700966973679102712707 103687051450460518654069061)
        ·
          refine ⟨19441322146961347247637949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103687051450460518654069061 19441322146961347247637949)
          ·
            refine ⟨7290495805110505217864231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19441322146961347247637949 7290495805110505217864231)
            ·
              refine ⟨10935743707665757826796347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290495805110505217864231 10935743707665757826796347)
              ·
                refine ⟨16403615561498636740194521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10935743707665757826796347 16403615561498636740194521)
                ·
                  refine ⟨12302711671123977555145891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16403615561498636740194521 12302711671123977555145891)
                  ·
                    refine ⟨18454067506685966332718837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12302711671123977555145891 18454067506685966332718837)
                    ·
                      refine ⟨1730068828751809343692391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18454067506685966332718837 1730068828751809343692391)
                      ·
                        rfl

theorem cell23_3369297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_3369297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369297 prefixEnd_3369297 := by exact prefixLift 3369297
  have htrace : WordTrace (prefixWord ++ tailWord_3369297) baseStart_3369297 baseEnd_3369297 := by
    simpa [prefixWord, tailWord_3369297, baseEnd_3369297] using wordTrace_append hprefix tailTrace_3369297
  have hstable : (prefixWord ++ tailWord_3369297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369297).length < 2 ^ (prefixWord ++ tailWord_3369297).sum := by decide
  have hdescent : baseEnd_3369297 < baseStart_3369297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369317 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 7]
def baseStart_3369317 : Nat := 118140960795 + 3369317 * 2 ^ 59
def prefixEnd_3369317 : Nat := 4983230072969 + 3 ^ 40 * 3369317 * 2
def baseEnd_3369317 : Nat := 192231010929433251715811

theorem tailTrace_3369317 : CollatzResearch.WordTrace tailWord_3369317 prefixEnd_3369317 192231010929433251715811 := by
  unfold tailWord_3369317
  simp only [CollatzResearch.WordTrace]
  refine ⟨122889086734547417376106205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81926057823031611584070803 122889086734547417376106205)
  ·
    refine ⟨46083407525455281516039827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122889086734547417376106205 46083407525455281516039827)
    ·
      refine ⟨69125111288182922274059741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46083407525455281516039827 69125111288182922274059741)
      ·
        refine ⟨25921916733068595852772403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69125111288182922274059741 25921916733068595852772403)
        ·
          refine ⟨38882875099602893779158605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25921916733068595852772403 38882875099602893779158605)
          ·
            refine ⟨14581078162351085167184477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38882875099602893779158605 14581078162351085167184477)
            ·
              refine ⟨5467904310881656937694179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14581078162351085167184477 5467904310881656937694179)
              ·
                refine ⟨8201856466322485406541269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5467904310881656937694179 8201856466322485406541269)
                ·
                  refine ⟨192231010929433251715811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8201856466322485406541269 192231010929433251715811)
                  ·
                    rfl

theorem cell23_3369317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_3369317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369317 prefixEnd_3369317 := by exact prefixLift 3369317
  have htrace : WordTrace (prefixWord ++ tailWord_3369317) baseStart_3369317 baseEnd_3369317 := by
    simpa [prefixWord, tailWord_3369317, baseEnd_3369317] using wordTrace_append hprefix tailTrace_3369317
  have hstable : (prefixWord ++ tailWord_3369317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369317).length < 2 ^ (prefixWord ++ tailWord_3369317).sum := by decide
  have hdescent : baseEnd_3369317 < baseStart_3369317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369328 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2]
def baseStart_3369328 : Nat := 118140960795 + 3369328 * 2 ^ 59
def prefixEnd_3369328 : Nat := 4983230072969 + 3 ^ 40 * 3369328 * 2
def baseEnd_3369328 : Nat := 1730084746652098722404749

theorem tailTrace_3369328 : CollatzResearch.WordTrace tailWord_3369328 prefixEnd_3369328 1730084746652098722404749 := by
  unfold tailWord_3369328
  simp only [CollatzResearch.WordTrace]
  refine ⟨61444743968753783127378319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81926325291671710836504425 61444743968753783127378319)
  ·
    refine ⟨92167115953130674691067479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61444743968753783127378319 92167115953130674691067479)
    ·
      refine ⟨138250673929696012036601219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92167115953130674691067479 138250673929696012036601219)
      ·
        refine ⟨207376010894544018054901829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138250673929696012036601219 207376010894544018054901829)
        ·
          refine ⟨38883002042727003385294093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207376010894544018054901829 38883002042727003385294093)
          ·
            refine ⟨14581125766022626269485285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38883002042727003385294093 14581125766022626269485285)
            ·
              refine ⟨2733961081129242425528491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14581125766022626269485285 2733961081129242425528491)
              ·
                refine ⟨4100941621693863638292737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2733961081129242425528491 4100941621693863638292737)
                ·
                  refine ⟨3075706216270397728719553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4100941621693863638292737 3075706216270397728719553)
                  ·
                    refine ⟨2306779662202798296539665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075706216270397728719553 2306779662202798296539665)
                    ·
                      refine ⟨1730084746652098722404749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306779662202798296539665 1730084746652098722404749)
                      ·
                        rfl

theorem cell23_3369328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 2, 2].length) (baseStart_3369328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369328 prefixEnd_3369328 := by exact prefixLift 3369328
  have htrace : WordTrace (prefixWord ++ tailWord_3369328) baseStart_3369328 baseEnd_3369328 := by
    simpa [prefixWord, tailWord_3369328, baseEnd_3369328] using wordTrace_append hprefix tailTrace_3369328
  have hstable : (prefixWord ++ tailWord_3369328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369328).length < 2 ^ (prefixWord ++ tailWord_3369328).sum := by decide
  have hdescent : baseEnd_3369328 < baseStart_3369328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369360 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 3, 10]
def baseStart_3369360 : Nat := 118140960795 + 3369360 * 2 ^ 59
def prefixEnd_3369360 : Nat := 4983230072969 + 3 ^ 40 * 3369360 * 2
def baseEnd_3369360 : Nat := 576700392677680865734867

theorem tailTrace_3369360 : CollatzResearch.WordTrace tailWord_3369360 prefixEnd_3369360 576700392677680865734867 := by
  unfold tailWord_3369360
  simp only [CollatzResearch.WordTrace]
  refine ⟨61445327536695817859960767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81927103382261090479947689 61445327536695817859960767)
  ·
    refine ⟨92167991305043726789941151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61445327536695817859960767 92167991305043726789941151)
    ·
      refine ⟨138251986957565590184911727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92167991305043726789941151 138251986957565590184911727)
      ·
        refine ⟨207377980436348385277367591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138251986957565590184911727 207377980436348385277367591)
        ·
          refine ⟨311066970654522577916051387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207377980436348385277367591 311066970654522577916051387)
          ·
            refine ⟨466600455981783866874077081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311066970654522577916051387 466600455981783866874077081)
            ·
              refine ⟨349950341986337900155557811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466600455981783866874077081 349950341986337900155557811)
              ·
                refine ⟨524925512979506850233336717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349950341986337900155557811 524925512979506850233336717)
                ·
                  refine ⟨196847067367315068837501269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 524925512979506850233336717 196847067367315068837501269)
                  ·
                    refine ⟨576700392677680865734867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 196847067367315068837501269 576700392677680865734867)
                    ·
                      rfl

theorem cell23_3369360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 3, 10].length) (baseStart_3369360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369360 prefixEnd_3369360 := by exact prefixLift 3369360
  have htrace : WordTrace (prefixWord ++ tailWord_3369360) baseStart_3369360 baseEnd_3369360 := by
    simpa [prefixWord, tailWord_3369360, baseEnd_3369360] using wordTrace_append hprefix tailTrace_3369360
  have hstable : (prefixWord ++ tailWord_3369360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369360).length < 2 ^ (prefixWord ++ tailWord_3369360).sum := by decide
  have hdescent : baseEnd_3369360 < baseStart_3369360 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369368 : List Nat := [2, 1, 2, 5, 1, 3, 2, 2, 5]
def baseStart_3369368 : Nat := 118140960795 + 3369368 * 2 ^ 59
def prefixEnd_3369368 : Nat := 4983230072969 + 3 ^ 40 * 3369368 * 2
def baseEnd_3369368 : Nat := 192233920653142062878285

theorem tailTrace_3369368 : CollatzResearch.WordTrace tailWord_3369368 prefixEnd_3369368 192233920653142062878285 := by
  unfold tailWord_3369368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61445473428681326543106379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81927297904908435390808505 61445473428681326543106379)
  ·
    refine ⟨92168210143021989814659569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61445473428681326543106379 92168210143021989814659569)
    ·
      refine ⟨69126157607266492360994677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92168210143021989814659569 69126157607266492360994677)
      ·
        refine ⟨6480577275681233658843251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69126157607266492360994677 6480577275681233658843251)
        ·
          refine ⟨9720865913521850488264877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6480577275681233658843251 9720865913521850488264877)
          ·
            refine ⟨3645324717570693933099329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9720865913521850488264877 3645324717570693933099329)
            ·
              refine ⟨2733993538178020449824497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3645324717570693933099329 2733993538178020449824497)
              ·
                refine ⟨2050495153633515337368373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2733993538178020449824497 2050495153633515337368373)
                ·
                  refine ⟨192233920653142062878285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2050495153633515337368373 192233920653142062878285)
                  ·
                    rfl

theorem cell23_3369368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 2, 5].length) (baseStart_3369368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369368 prefixEnd_3369368 := by exact prefixLift 3369368
  have htrace : WordTrace (prefixWord ++ tailWord_3369368) baseStart_3369368 baseEnd_3369368 := by
    simpa [prefixWord, tailWord_3369368, baseEnd_3369368] using wordTrace_append hprefix tailTrace_3369368
  have hstable : (prefixWord ++ tailWord_3369368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369368).length < 2 ^ (prefixWord ++ tailWord_3369368).sum := by decide
  have hdescent : baseEnd_3369368 < baseStart_3369368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369394 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 3, 4]
def baseStart_3369394 : Nat := 118140960795 + 3369394 * 2 ^ 59
def prefixEnd_3369394 : Nat := 4983230072969 + 3 ^ 40 * 3369394 * 2
def baseEnd_3369394 : Nat := 576706212125098488059815

theorem tailTrace_3369394 : CollatzResearch.WordTrace tailWord_3369394 prefixEnd_3369394 576706212125098488059815 := by
  unfold tailWord_3369394
  simp only [CollatzResearch.WordTrace]
  refine ⟨30722973788817114881664809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81927930103512306351106157 30722973788817114881664809)
  ·
    refine ⟨23042230341612836161248607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30722973788817114881664809 23042230341612836161248607)
    ·
      refine ⟨34563345512419254241872911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23042230341612836161248607 34563345512419254241872911)
      ·
        refine ⟨51845018268628881362809367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34563345512419254241872911 51845018268628881362809367)
        ·
          refine ⟨77767527402943322044214051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51845018268628881362809367 77767527402943322044214051)
          ·
            refine ⟨116651291104414983066321077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77767527402943322044214051 116651291104414983066321077)
            ·
              refine ⟨10936058541038904662467601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116651291104414983066321077 10936058541038904662467601)
              ·
                refine ⟨8202043905779178496850701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10936058541038904662467601 8202043905779178496850701)
                ·
                  refine ⟨3075766464667191936319013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8202043905779178496850701 3075766464667191936319013)
                  ·
                    refine ⟨576706212125098488059815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075766464667191936319013 576706212125098488059815)
                    ·
                      rfl

theorem cell23_3369394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 3, 4].length) (baseStart_3369394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369394 prefixEnd_3369394 := by exact prefixLift 3369394
  have htrace : WordTrace (prefixWord ++ tailWord_3369394) baseStart_3369394 baseEnd_3369394 := by
    simpa [prefixWord, tailWord_3369394, baseEnd_3369394] using wordTrace_append hprefix tailTrace_3369394
  have hstable : (prefixWord ++ tailWord_3369394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369394).length < 2 ^ (prefixWord ++ tailWord_3369394).sum := by decide
  have hdescent : baseEnd_3369394 < baseStart_3369394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369401 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 4]
def baseStart_3369401 : Nat := 118140960795 + 3369401 * 2 ^ 59
def prefixEnd_3369401 : Nat := 4983230072969 + 3 ^ 40 * 3369401 * 2
def baseEnd_3369401 : Nat := 1730122230739876936791913

theorem tailTrace_3369401 : CollatzResearch.WordTrace tailWord_3369401 prefixEnd_3369401 1730122230739876936791913 := by
  unfold tailWord_3369401
  simp only [CollatzResearch.WordTrace]
  refine ⟨122892150466243099722164057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81928100310828733148109371 122892150466243099722164057)
  ·
    refine ⟨92169112849682324791623043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122892150466243099722164057 92169112849682324791623043)
    ·
      refine ⟨138253669274523487187434565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92169112849682324791623043 138253669274523487187434565)
      ·
        refine ⟨25922562988973153847643981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138253669274523487187434565 25922562988973153847643981)
        ·
          refine ⟨9720961120864932692866493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25922562988973153847643981 9720961120864932692866493)
          ·
            refine ⟨3645360420324349759824935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9720961120864932692866493 3645360420324349759824935)
            ·
              refine ⟨5468040630486524639737403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3645360420324349759824935 5468040630486524639737403)
              ·
                refine ⟨8202060945729786959606105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468040630486524639737403 8202060945729786959606105)
                ·
                  refine ⟨6151545709297340219704579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202060945729786959606105 6151545709297340219704579)
                  ·
                    refine ⟨9227318563946010329556869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151545709297340219704579 9227318563946010329556869)
                    ·
                      refine ⟨1730122230739876936791913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9227318563946010329556869 1730122230739876936791913)
                      ·
                        rfl

theorem cell23_3369401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_3369401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369401 prefixEnd_3369401 := by exact prefixLift 3369401
  have htrace : WordTrace (prefixWord ++ tailWord_3369401) baseStart_3369401 baseEnd_3369401 := by
    simpa [prefixWord, tailWord_3369401, baseEnd_3369401] using wordTrace_append hprefix tailTrace_3369401
  have hstable : (prefixWord ++ tailWord_3369401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369401).length < 2 ^ (prefixWord ++ tailWord_3369401).sum := by decide
  have hdescent : baseEnd_3369401 < baseStart_3369401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369428 : List Nat := [2, 4, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_3369428 : Nat := 118140960795 + 3369428 * 2 ^ 59
def prefixEnd_3369428 : Nat := 4983230072969 + 3 ^ 40 * 3369428 * 2
def baseEnd_3369428 : Nat := 576712031572516110384763

theorem tailTrace_3369428 : CollatzResearch.WordTrace tailWord_3369428 prefixEnd_3369428 576712031572516110384763 := by
  unfold tailWord_3369428
  simp only [CollatzResearch.WordTrace]
  refine ⟨61446567618572641666698469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81928756824763522222264625 61446567618572641666698469)
  ·
    refine ⟨11521231428482370312505963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61446567618572641666698469 11521231428482370312505963)
    ·
      refine ⟨17281847142723555468758945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11521231428482370312505963 17281847142723555468758945)
      ·
        refine ⟨12961385357042666601569209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17281847142723555468758945 12961385357042666601569209)
        ·
          refine ⟨9721039017781999951176907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12961385357042666601569209 9721039017781999951176907)
          ·
            refine ⟨14581558526672999926765361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9721039017781999951176907 14581558526672999926765361)
            ·
              refine ⟨10936168895004749945074021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14581558526672999926765361 10936168895004749945074021)
              ·
                refine ⟨2050531667813390614701379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10936168895004749945074021 2050531667813390614701379)
                ·
                  refine ⟨3075797501720085922052069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050531667813390614701379 3075797501720085922052069)
                  ·
                    refine ⟨576712031572516110384763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3075797501720085922052069 576712031572516110384763)
                    ·
                      rfl

theorem cell23_3369428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_3369428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369428 prefixEnd_3369428 := by exact prefixLift 3369428
  have htrace : WordTrace (prefixWord ++ tailWord_3369428) baseStart_3369428 baseEnd_3369428 := by
    simpa [prefixWord, tailWord_3369428, baseEnd_3369428] using wordTrace_append hprefix tailTrace_3369428
  have hstable : (prefixWord ++ tailWord_3369428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369428).length < 2 ^ (prefixWord ++ tailWord_3369428).sum := by decide
  have hdescent : baseEnd_3369428 < baseStart_3369428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369487 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6]
def baseStart_3369487 : Nat := 118140960795 + 3369487 * 2 ^ 59
def prefixEnd_3369487 : Nat := 4983230072969 + 3 ^ 40 * 3369487 * 2
def baseEnd_3369487 : Nat := 1730166390076163600316517

theorem tailTrace_3369487 : CollatzResearch.WordTrace tailWord_3369487 prefixEnd_3369487 1730166390076163600316517 := by
  unfold tailWord_3369487
  simp only [CollatzResearch.WordTrace]
  refine ⟨122895287143931536409794715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81930191429287690939863143 122895287143931536409794715)
  ·
    refine ⟨184342930715897304614692073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122895287143931536409794715 184342930715897304614692073)
    ·
      refine ⟨138257198036922978461019055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184342930715897304614692073 138257198036922978461019055)
      ·
        refine ⟨207385797055384467691528583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138257198036922978461019055 207385797055384467691528583)
        ·
          refine ⟨311078695583076701537292875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207385797055384467691528583 311078695583076701537292875)
          ·
            refine ⟨466618043374615052305939313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311078695583076701537292875 466618043374615052305939313)
            ·
              refine ⟨349963532530961289229454485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 466618043374615052305939313 349963532530961289229454485)
              ·
                refine ⟨16404540587388810432630679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 349963532530961289229454485 16404540587388810432630679)
                ·
                  refine ⟨24606810881083215648946019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16404540587388810432630679 24606810881083215648946019)
                  ·
                    refine ⟨36910216321624823473419029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24606810881083215648946019 36910216321624823473419029)
                    ·
                      refine ⟨1730166390076163600316517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36910216321624823473419029 1730166390076163600316517)
                      ·
                        rfl

theorem cell23_3369487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_3369487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369487 prefixEnd_3369487 := by exact prefixLift 3369487
  have htrace : WordTrace (prefixWord ++ tailWord_3369487) baseStart_3369487 baseEnd_3369487 := by
    simpa [prefixWord, tailWord_3369487, baseEnd_3369487] using wordTrace_append hprefix tailTrace_3369487
  have hstable : (prefixWord ++ tailWord_3369487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369487).length < 2 ^ (prefixWord ++ tailWord_3369487).sum := by decide
  have hdescent : baseEnd_3369487 < baseStart_3369487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369508 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_3369508 : Nat := 118140960795 + 3369508 * 2 ^ 59
def prefixEnd_3369508 : Nat := 4983230072969 + 3 ^ 40 * 3369508 * 2
def baseEnd_3369508 : Nat := 1730177173169908018153921

theorem tailTrace_3369508 : CollatzResearch.WordTrace tailWord_3369508 prefixEnd_3369508 1730177173169908018153921 := by
  unfold tailWord_3369508
  simp only [CollatzResearch.WordTrace]
  refine ⟨61448026538427728498154589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81930702051236971330872785 61448026538427728498154589)
  ·
    refine ⟨23043009951910398186807971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61448026538427728498154589 23043009951910398186807971)
    ·
      refine ⟨34564514927865597280211957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23043009951910398186807971 34564514927865597280211957)
      ·
        refine ⟨3240423274487399745019871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34564514927865597280211957 3240423274487399745019871)
        ·
          refine ⟨4860634911731099617529807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240423274487399745019871 4860634911731099617529807)
          ·
            refine ⟨7290952367596649426294711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860634911731099617529807 7290952367596649426294711)
            ·
              refine ⟨10936428551394974139442067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7290952367596649426294711 10936428551394974139442067)
              ·
                refine ⟨16404642827092461209163101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936428551394974139442067 16404642827092461209163101)
                ·
                  refine ⟨6151741060159672953436163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16404642827092461209163101 6151741060159672953436163)
                  ·
                    refine ⟨9227611590239509430154245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6151741060159672953436163 9227611590239509430154245)
                    ·
                      refine ⟨1730177173169908018153921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9227611590239509430154245 1730177173169908018153921)
                      ·
                        rfl

theorem cell23_3369508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_3369508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369508 prefixEnd_3369508 := by exact prefixLift 3369508
  have htrace : WordTrace (prefixWord ++ tailWord_3369508) baseStart_3369508 baseEnd_3369508 := by
    simpa [prefixWord, tailWord_3369508, baseEnd_3369508] using wordTrace_append hprefix tailTrace_3369508
  have hstable : (prefixWord ++ tailWord_3369508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369508).length < 2 ^ (prefixWord ++ tailWord_3369508).sum := by decide
  have hdescent : baseEnd_3369508 < baseStart_3369508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369514 : List Nat := [3, 1, 4, 1, 1, 2, 2, 9]
def baseStart_3369514 : Nat := 118140960795 + 3369514 * 2 ^ 59
def prefixEnd_3369514 : Nat := 4983230072969 + 3 ^ 40 * 3369514 * 2
def baseEnd_3369514 : Nat := 64080750150142036839959

theorem tailTrace_3369514 : CollatzResearch.WordTrace tailWord_3369514 prefixEnd_3369514 64080750150142036839959 := by
  unfold tailWord_3369514
  simp only [CollatzResearch.WordTrace]
  refine ⟨30724067978708430005256899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81930847943222480014018397 30724067978708430005256899)
  ·
    refine ⟨46086101968062645007885349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30724067978708430005256899 46086101968062645007885349)
    ·
      refine ⟨8641144119011745938978503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46086101968062645007885349 8641144119011745938978503)
      ·
        refine ⟨12961716178517618908467755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8641144119011745938978503 12961716178517618908467755)
        ·
          refine ⟨19442574267776428362701633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12961716178517618908467755 19442574267776428362701633)
          ·
            refine ⟨14581930700832321272026225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19442574267776428362701633 14581930700832321272026225)
            ·
              refine ⟨10936448025624240954019669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14581930700832321272026225 10936448025624240954019669)
              ·
                refine ⟨64080750150142036839959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10936448025624240954019669 64080750150142036839959)
                ·
                  rfl

theorem cell23_3369514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 9].length) (baseStart_3369514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369514 prefixEnd_3369514 := by exact prefixLift 3369514
  have htrace : WordTrace (prefixWord ++ tailWord_3369514) baseStart_3369514 baseEnd_3369514 := by
    simpa [prefixWord, tailWord_3369514, baseEnd_3369514] using wordTrace_append hprefix tailTrace_3369514
  have hstable : (prefixWord ++ tailWord_3369514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369514).length < 2 ^ (prefixWord ++ tailWord_3369514).sum := by decide
  have hdescent : baseEnd_3369514 < baseStart_3369514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369525 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_3369525 : Nat := 118140960795 + 3369525 * 2 ^ 59
def prefixEnd_3369525 : Nat := 4983230072969 + 3 ^ 40 * 3369525 * 2
def baseEnd_3369525 : Nat := 1730185902341034451641343

theorem tailTrace_3369525 : CollatzResearch.WordTrace tailWord_3369525 prefixEnd_3369525 1730185902341034451641343 := by
  unfold tailWord_3369525
  simp only [CollatzResearch.WordTrace]
  refine ⟨122896673117793868899678029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81931115411862579266452019 122896673117793868899678029)
  ·
    refine ⟨46086252419172700837379261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122896673117793868899678029 46086252419172700837379261)
    ·
      refine ⟨17282344657189762814017223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46086252419172700837379261 17282344657189762814017223)
      ·
        refine ⟨25923516985784644221025835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17282344657189762814017223 25923516985784644221025835)
        ·
          refine ⟨38885275478676966331538753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25923516985784644221025835 38885275478676966331538753)
          ·
            refine ⟨29163956609007724748654065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38885275478676966331538753 29163956609007724748654065)
            ·
              refine ⟨21872967456755793561490549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29163956609007724748654065 21872967456755793561490549)
              ·
                refine ⟨2050590699070855646389739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21872967456755793561490549 2050590699070855646389739)
                ·
                  refine ⟨3075886048606283469584609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2050590699070855646389739 3075886048606283469584609)
                  ·
                    refine ⟨2306914536454712602188457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3075886048606283469584609 2306914536454712602188457)
                    ·
                      refine ⟨1730185902341034451641343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306914536454712602188457 1730185902341034451641343)
                      ·
                        rfl

theorem cell23_3369525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_3369525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369525 prefixEnd_3369525 := by exact prefixLift 3369525
  have htrace : WordTrace (prefixWord ++ tailWord_3369525) baseStart_3369525 baseEnd_3369525 := by
    simpa [prefixWord, tailWord_3369525, baseEnd_3369525] using wordTrace_append hprefix tailTrace_3369525
  have hstable : (prefixWord ++ tailWord_3369525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369525).length < 2 ^ (prefixWord ++ tailWord_3369525).sum := by decide
  have hdescent : baseEnd_3369525 < baseStart_3369525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369528 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3]
def baseStart_3369528 : Nat := 118140960795 + 3369528 * 2 ^ 59
def prefixEnd_3369528 : Nat := 4983230072969 + 3 ^ 40 * 3369528 * 2
def baseEnd_3369528 : Nat := 1730187442782997939903829

theorem tailTrace_3369528 : CollatzResearch.WordTrace tailWord_3369528 prefixEnd_3369528 1730187442782997939903829 := by
  unfold tailWord_3369528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61448391268391500206018619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81931188357855333608024825 61448391268391500206018619)
  ·
    refine ⟨92172586902587250309027929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61448391268391500206018619 92172586902587250309027929)
    ·
      refine ⟨69129440176940437731770947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92172586902587250309027929 69129440176940437731770947)
      ·
        refine ⟨103694160265410656597656421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69129440176940437731770947 103694160265410656597656421)
        ·
          refine ⟨19442655049764498112060579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103694160265410656597656421 19442655049764498112060579)
          ·
            refine ⟨29163982574646747168090869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19442655049764498112060579 29163982574646747168090869)
            ·
              refine ⟨2734123366373132547008519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29163982574646747168090869 2734123366373132547008519)
              ·
                refine ⟨4101185049559698820512779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734123366373132547008519 4101185049559698820512779)
                ·
                  refine ⟨6151777574339548230769169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101185049559698820512779 6151777574339548230769169)
                  ·
                    refine ⟨4613833180754661173076877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6151777574339548230769169 4613833180754661173076877)
                    ·
                      refine ⟨1730187442782997939903829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4613833180754661173076877 1730187442782997939903829)
                      ·
                        rfl

theorem cell23_3369528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_3369528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369528 prefixEnd_3369528 := by exact prefixLift 3369528
  have htrace : WordTrace (prefixWord ++ tailWord_3369528) baseStart_3369528 baseEnd_3369528 := by
    simpa [prefixWord, tailWord_3369528, baseEnd_3369528] using wordTrace_append hprefix tailTrace_3369528
  have hstable : (prefixWord ++ tailWord_3369528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369528).length < 2 ^ (prefixWord ++ tailWord_3369528).sum := by decide
  have hdescent : baseEnd_3369528 < baseStart_3369528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369551 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 3, 3, 2]
def baseStart_3369551 : Nat := 118140960795 + 3369551 * 2 ^ 59
def prefixEnd_3369551 : Nat := 4983230072969 + 3 ^ 40 * 3369551 * 2
def baseEnd_3369551 : Nat := 1730199252838051349916223

theorem tailTrace_3369551 : CollatzResearch.WordTrace tailWord_3369551 prefixEnd_3369551 1730199252838051349916223 := by
  unfold tailWord_3369551
  simp only [CollatzResearch.WordTrace]
  refine ⟨122897621415699675340124507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81931747610466450226749671 122897621415699675340124507)
  ·
    refine ⟨184346432123549513010186761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122897621415699675340124507 184346432123549513010186761)
    ·
      refine ⟨138259824092662134757640071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184346432123549513010186761 138259824092662134757640071)
      ·
        refine ⟨207389736138993202136460107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138259824092662134757640071 207389736138993202136460107)
        ·
          refine ⟨311084604208489803204690161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207389736138993202136460107 311084604208489803204690161)
          ·
            refine ⟨233313453156367352403517621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311084604208489803204690161 233313453156367352403517621)
            ·
              refine ⟨21873136233409439287829777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233313453156367352403517621 21873136233409439287829777)
              ·
                refine ⟨16404852175057079465872333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21873136233409439287829777 16404852175057079465872333)
                ·
                  refine ⟨6151819565646404799702125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16404852175057079465872333 6151819565646404799702125)
                  ·
                    refine ⟨2306932337117401799888297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6151819565646404799702125 2306932337117401799888297)
                    ·
                      refine ⟨1730199252838051349916223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2306932337117401799888297 1730199252838051349916223)
                      ·
                        rfl

theorem cell23_3369551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 3, 2].length) (baseStart_3369551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369551 prefixEnd_3369551 := by exact prefixLift 3369551
  have htrace : WordTrace (prefixWord ++ tailWord_3369551) baseStart_3369551 baseEnd_3369551 := by
    simpa [prefixWord, tailWord_3369551, baseEnd_3369551] using wordTrace_append hprefix tailTrace_3369551
  have hstable : (prefixWord ++ tailWord_3369551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369551).length < 2 ^ (prefixWord ++ tailWord_3369551).sum := by decide
  have hdescent : baseEnd_3369551 < baseStart_3369551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369651 : List Nat := [1, 1, 1, 2, 3, 5, 1, 2, 2, 5]
def baseStart_3369651 : Nat := 118140960795 + 3369651 * 2 ^ 59
def prefixEnd_3369651 : Nat := 4983230072969 + 3 ^ 40 * 3369651 * 2
def baseEnd_3369651 : Nat := 576750200301166986221921

theorem tailTrace_3369651 : CollatzResearch.WordTrace tailWord_3369651 prefixEnd_3369651 576750200301166986221921 := by
  unfold tailWord_3369651
  simp only [CollatzResearch.WordTrace]
  refine ⟨122901268715337392418764807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81934179143558261612509871 122901268715337392418764807)
  ·
    refine ⟨184351903073006088628147211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122901268715337392418764807 184351903073006088628147211)
    ·
      refine ⟨276527854609509132942220817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184351903073006088628147211 276527854609509132942220817)
      ·
        refine ⟨207395890957131849706665613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276527854609509132942220817 207395890957131849706665613)
        ·
          refine ⟨77773459108924443639999605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207395890957131849706665613 77773459108924443639999605)
          ·
            refine ⟨7291261791461666591249963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77773459108924443639999605 7291261791461666591249963)
            ·
              refine ⟨10936892687192499886874945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291261791461666591249963 10936892687192499886874945)
              ·
                refine ⟨8202669515394374915156209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10936892687192499886874945 8202669515394374915156209)
                ·
                  refine ⟨6152002136545781186367157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202669515394374915156209 6152002136545781186367157)
                  ·
                    refine ⟨576750200301166986221921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6152002136545781186367157 576750200301166986221921)
                    ·
                      rfl

theorem cell23_3369651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2, 5].length) (baseStart_3369651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369651 prefixEnd_3369651 := by exact prefixLift 3369651
  have htrace : WordTrace (prefixWord ++ tailWord_3369651) baseStart_3369651 baseEnd_3369651 := by
    simpa [prefixWord, tailWord_3369651, baseEnd_3369651] using wordTrace_append hprefix tailTrace_3369651
  have hstable : (prefixWord ++ tailWord_3369651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369651).length < 2 ^ (prefixWord ++ tailWord_3369651).sum := by decide
  have hdescent : baseEnd_3369651 < baseStart_3369651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369655 : List Nat := [1, 1, 3, 1, 6, 1, 3, 2, 5]
def baseStart_3369655 : Nat := 118140960795 + 3369655 * 2 ^ 59
def prefixEnd_3369655 : Nat := 4983230072969 + 3 ^ 40 * 3369655 * 2
def baseEnd_3369655 : Nat := 192250294980679882557305

theorem tailTrace_3369655 : CollatzResearch.WordTrace tailWord_3369655 prefixEnd_3369655 192250294980679882557305 := by
  unfold tailWord_3369655
  simp only [CollatzResearch.WordTrace]
  refine ⟨122901414607322901101910419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81934276404881934067940279 122901414607322901101910419)
  ·
    refine ⟨184352121910984351652865629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122901414607322901101910419 184352121910984351652865629)
    ·
      refine ⟨69132045716619131869824611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184352121910984351652865629 69132045716619131869824611)
      ·
        refine ⟨103698068574928697804736917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69132045716619131869824611 103698068574928697804736917)
        ·
          refine ⟨4860846964449782709597043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103698068574928697804736917 4860846964449782709597043)
          ·
            refine ⟨7291270446674674064395565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860846964449782709597043 7291270446674674064395565)
            ·
              refine ⟨2734226417503002774148337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7291270446674674064395565 2734226417503002774148337)
              ·
                refine ⟨2050669813127252080611253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734226417503002774148337 2050669813127252080611253)
                ·
                  refine ⟨192250294980679882557305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2050669813127252080611253 192250294980679882557305)
                  ·
                    rfl

theorem cell23_3369655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 5].length) (baseStart_3369655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369655 prefixEnd_3369655 := by exact prefixLift 3369655
  have htrace : WordTrace (prefixWord ++ tailWord_3369655) baseStart_3369655 baseEnd_3369655 := by
    simpa [prefixWord, tailWord_3369655, baseEnd_3369655] using wordTrace_append hprefix tailTrace_3369655
  have hstable : (prefixWord ++ tailWord_3369655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369655).length < 2 ^ (prefixWord ++ tailWord_3369655).sum := by decide
  have hdescent : baseEnd_3369655 < baseStart_3369655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369661 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 5]
def baseStart_3369661 : Nat := 118140960795 + 3369661 * 2 ^ 59
def prefixEnd_3369661 : Nat := 4983230072969 + 3 ^ 40 * 3369661 * 2
def baseEnd_3369661 : Nat := 1730255735710045919540717

theorem tailTrace_3369661 : CollatzResearch.WordTrace tailWord_3369661 prefixEnd_3369661 1730255735710045919540717 := by
  unfold tailWord_3369661
  simp only [CollatzResearch.WordTrace]
  refine ⟨122901633445301164126628837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81934422296867442751085891 122901633445301164126628837)
  ·
    refine ⟨23044056270993968273742907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122901633445301164126628837 23044056270993968273742907)
    ·
      refine ⟨34566084406490952410614361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23044056270993968273742907 34566084406490952410614361)
      ·
        refine ⟨25924563304868214307960771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34566084406490952410614361 25924563304868214307960771)
        ·
          refine ⟨38886844957302321461941157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25924563304868214307960771 38886844957302321461941157)
          ·
            refine ⟨7291283429494185274113967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38886844957302321461941157 7291283429494185274113967)
            ·
              refine ⟨10936925144241277911170951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291283429494185274113967 10936925144241277911170951)
              ·
                refine ⟨16405387716361916866756427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10936925144241277911170951 16405387716361916866756427)
                ·
                  refine ⟨24608081574542875300134641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16405387716361916866756427 24608081574542875300134641)
                  ·
                    refine ⟨18456061180907156475100981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24608081574542875300134641 18456061180907156475100981)
                    ·
                      refine ⟨1730255735710045919540717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18456061180907156475100981 1730255735710045919540717)
                      ·
                        rfl

theorem cell23_3369661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_3369661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369661 prefixEnd_3369661 := by exact prefixLift 3369661
  have htrace : WordTrace (prefixWord ++ tailWord_3369661) baseStart_3369661 baseEnd_3369661 := by
    simpa [prefixWord, tailWord_3369661, baseEnd_3369661] using wordTrace_append hprefix tailTrace_3369661
  have hstable : (prefixWord ++ tailWord_3369661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369661).length < 2 ^ (prefixWord ++ tailWord_3369661).sum := by decide
  have hdescent : baseEnd_3369661 < baseStart_3369661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369681 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_3369681 : Nat := 118140960795 + 3369681 * 2 ^ 59
def prefixEnd_3369681 : Nat := 4983230072969 + 3 ^ 40 * 3369681 * 2
def baseEnd_3369681 : Nat := 576755335107711947096875

theorem tailTrace_3369681 : CollatzResearch.WordTrace tailWord_3369681 prefixEnd_3369681 576755335107711947096875 := by
  unfold tailWord_3369681
  simp only [CollatzResearch.WordTrace]
  refine ⟨122902362905228707542356897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81934908603485805028237931 122902362905228707542356897)
  ·
    refine ⟨92176772178921530656767673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122902362905228707542356897 92176772178921530656767673)
    ·
      refine ⟨69132579134191147992575755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92176772178921530656767673 69132579134191147992575755)
      ·
        refine ⟨103698868701286721988863633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69132579134191147992575755 103698868701286721988863633)
        ·
          refine ⟨77774151525965041491647725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103698868701286721988863633 77774151525965041491647725)
          ·
            refine ⟨29165306822236890559367897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77774151525965041491647725 29165306822236890559367897)
            ·
              refine ⟨21873980116677667919525923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29165306822236890559367897 21873980116677667919525923)
              ·
                refine ⟨32810970175016501879288885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21873980116677667919525923 32810970175016501879288885)
                ·
                  refine ⟨3076028453907797051183333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32810970175016501879288885 3076028453907797051183333)
                  ·
                    refine ⟨576755335107711947096875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076028453907797051183333 576755335107711947096875)
                    ·
                      rfl

theorem cell23_3369681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_3369681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369681 prefixEnd_3369681 := by exact prefixLift 3369681
  have htrace : WordTrace (prefixWord ++ tailWord_3369681) baseStart_3369681 baseEnd_3369681 := by
    simpa [prefixWord, tailWord_3369681, baseEnd_3369681] using wordTrace_append hprefix tailTrace_3369681
  have hstable : (prefixWord ++ tailWord_3369681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369681).length < 2 ^ (prefixWord ++ tailWord_3369681).sum := by decide
  have hdescent : baseEnd_3369681 < baseStart_3369681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369685 : List Nat := [1, 3, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3369685 : Nat := 118140960795 + 3369685 * 2 ^ 59
def prefixEnd_3369685 : Nat := 4983230072969 + 3 ^ 40 * 3369685 * 2
def baseEnd_3369685 : Nat := 576756019748584608546869

theorem tailTrace_3369685 : CollatzResearch.WordTrace tailWord_3369685 prefixEnd_3369685 576756019748584608546869 := by
  unfold tailWord_3369685
  simp only [CollatzResearch.WordTrace]
  refine ⟨122902508797214216225502509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81935005864809477483668339 122902508797214216225502509)
  ·
    refine ⟨46088440798955331084563441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122902508797214216225502509 46088440798955331084563441)
    ·
      refine ⟨34566330599216498313422581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46088440798955331084563441 34566330599216498313422581)
      ·
        refine ⟨3240593493676546716883367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34566330599216498313422581 3240593493676546716883367)
        ·
          refine ⟨4860890240514820075325051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3240593493676546716883367 4860890240514820075325051)
          ·
            refine ⟨7291335360772230112987577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4860890240514820075325051 7291335360772230112987577)
            ·
              refine ⟨5468501520579172584740683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291335360772230112987577 5468501520579172584740683)
              ·
                refine ⟨8202752280868758877111025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468501520579172584740683 8202752280868758877111025)
                ·
                  refine ⟨6152064210651569157833269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202752280868758877111025 6152064210651569157833269)
                  ·
                    refine ⟨576756019748584608546869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6152064210651569157833269 576756019748584608546869)
                    ·
                      rfl

theorem cell23_3369685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3369685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369685 prefixEnd_3369685 := by exact prefixLift 3369685
  have htrace : WordTrace (prefixWord ++ tailWord_3369685) baseStart_3369685 baseEnd_3369685 := by
    simpa [prefixWord, tailWord_3369685, baseEnd_3369685] using wordTrace_append hprefix tailTrace_3369685
  have hstable : (prefixWord ++ tailWord_3369685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369685).length < 2 ^ (prefixWord ++ tailWord_3369685).sum := by decide
  have hdescent : baseEnd_3369685 < baseStart_3369685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369688 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4]
def baseStart_3369688 : Nat := 118140960795 + 3369688 * 2 ^ 59
def prefixEnd_3369688 : Nat := 4983230072969 + 3 ^ 40 * 3369688 * 2
def baseEnd_3369688 : Nat := 1730269599687717313903093

theorem tailTrace_3369688 : CollatzResearch.WordTrace tailWord_3369688 prefixEnd_3369688 1730269599687717313903093 := by
  unfold tailWord_3369688
  simp only [CollatzResearch.WordTrace]
  refine ⟨61451309108101673868930859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81935078810802231825241145 61451309108101673868930859)
  ·
    refine ⟨92176963662152510803396289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61451309108101673868930859 92176963662152510803396289)
    ·
      refine ⟨69132722746614383102547217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92176963662152510803396289 69132722746614383102547217)
      ·
        refine ⟨51849542059960787326910413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69132722746614383102547217 51849542059960787326910413)
        ·
          refine ⟨19443578272485295247591405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51849542059960787326910413 19443578272485295247591405)
          ·
            refine ⟨7291341852181985717846777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19443578272485295247591405 7291341852181985717846777)
            ·
              refine ⟨5468506389136489288385083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291341852181985717846777 5468506389136489288385083)
              ·
                refine ⟨8202759583704733932577625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468506389136489288385083 8202759583704733932577625)
                ·
                  refine ⟨6152069687778550449433219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8202759583704733932577625 6152069687778550449433219)
                  ·
                    refine ⟨9228104531667825674149829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152069687778550449433219 9228104531667825674149829)
                    ·
                      refine ⟨1730269599687717313903093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9228104531667825674149829 1730269599687717313903093)
                      ·
                        rfl

theorem cell23_3369688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_3369688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369688 prefixEnd_3369688 := by exact prefixLift 3369688
  have htrace : WordTrace (prefixWord ++ tailWord_3369688) baseStart_3369688 baseEnd_3369688 := by
    simpa [prefixWord, tailWord_3369688, baseEnd_3369688] using wordTrace_append hprefix tailTrace_3369688
  have hstable : (prefixWord ++ tailWord_3369688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369688).length < 2 ^ (prefixWord ++ tailWord_3369688).sum := by decide
  have hdescent : baseEnd_3369688 < baseStart_3369688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369711 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 6]
def baseStart_3369711 : Nat := 118140960795 + 3369711 * 2 ^ 59
def prefixEnd_3369711 : Nat := 4983230072969 + 3 ^ 40 * 3369711 * 2
def baseEnd_3369711 : Nat := 192253489971418969323943

theorem tailTrace_3369711 : CollatzResearch.WordTrace tailWord_3369711 prefixEnd_3369711 192253489971418969323943 := by
  unfold tailWord_3369711
  simp only [CollatzResearch.WordTrace]
  refine ⟨122903457095120022665948987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81935638063413348443965991 122903457095120022665948987)
  ·
    refine ⟨184355185642680033998923481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122903457095120022665948987 184355185642680033998923481)
    ·
      refine ⟨138266389232010025499192611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184355185642680033998923481 138266389232010025499192611)
      ·
        refine ⟨207399583848015038248788917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138266389232010025499192611 207399583848015038248788917)
        ·
          refine ⟨19443710985751409835823961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 207399583848015038248788917 19443710985751409835823961)
          ·
            refine ⟨14582783239313557376867971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19443710985751409835823961 14582783239313557376867971)
            ·
              refine ⟨21874174858970336065301957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14582783239313557376867971 21874174858970336065301957)
              ·
                refine ⟨4101407786056938012244117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21874174858970336065301957 4101407786056938012244117)
                ·
                  refine ⟨192253489971418969323943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4101407786056938012244117 192253489971418969323943)
                  ·
                    rfl

theorem cell23_3369711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 6].length) (baseStart_3369711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369711 prefixEnd_3369711 := by exact prefixLift 3369711
  have htrace : WordTrace (prefixWord ++ tailWord_3369711) baseStart_3369711 baseEnd_3369711 := by
    simpa [prefixWord, tailWord_3369711, baseEnd_3369711] using wordTrace_append hprefix tailTrace_3369711
  have hstable : (prefixWord ++ tailWord_3369711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369711).length < 2 ^ (prefixWord ++ tailWord_3369711).sum := by decide
  have hdescent : baseEnd_3369711 < baseStart_3369711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369795 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 3, 2, 2]
def baseStart_3369795 : Nat := 118140960795 + 3369795 * 2 ^ 59
def prefixEnd_3369795 : Nat := 4983230072969 + 3 ^ 40 * 3369795 * 2
def baseEnd_3369795 : Nat := 1730324542117748395265101

theorem tailTrace_3369795 : CollatzResearch.WordTrace tailWord_3369795 prefixEnd_3369795 1730324542117748395265101 := by
  unfold tailWord_3369795
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906520826815705012006839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81937680551210470008004559 122906520826815705012006839)
  ·
    refine ⟨184359781240223557518010259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122906520826815705012006839 184359781240223557518010259)
    ·
      refine ⟨276539671860335336277015389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184359781240223557518010259 276539671860335336277015389)
      ·
        refine ⟨103702376947625751103880771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276539671860335336277015389 103702376947625751103880771)
        ·
          refine ⟨155553565421438626655821157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103702376947625751103880771 155553565421438626655821157)
          ·
            refine ⟨29166293516519742497966467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155553565421438626655821157 29166293516519742497966467)
            ·
              refine ⟨43749440274779613746949701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29166293516519742497966467 43749440274779613746949701)
              ·
                refine ⟨8203020051521177577553069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43749440274779613746949701 8203020051521177577553069)
                ·
                  refine ⟨3076132519320441591582401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8203020051521177577553069 3076132519320441591582401)
                  ·
                    refine ⟨2307099389490331193686801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3076132519320441591582401 2307099389490331193686801)
                    ·
                      refine ⟨1730324542117748395265101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307099389490331193686801 1730324542117748395265101)
                      ·
                        rfl

theorem cell23_3369795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_3369795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369795 prefixEnd_3369795 := by exact prefixLift 3369795
  have htrace : WordTrace (prefixWord ++ tailWord_3369795) baseStart_3369795 baseEnd_3369795 := by
    simpa [prefixWord, tailWord_3369795, baseEnd_3369795] using wordTrace_append hprefix tailTrace_3369795
  have hstable : (prefixWord ++ tailWord_3369795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369795).length < 2 ^ (prefixWord ++ tailWord_3369795).sum := by decide
  have hdescent : baseEnd_3369795 < baseStart_3369795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369801 : List Nat := [1, 2, 1, 1, 2, 6, 1, 9]
def baseStart_3369801 : Nat := 118140960795 + 3369801 * 2 ^ 59
def prefixEnd_3369801 : Nat := 4983230072969 + 3 ^ 40 * 3369801 * 2
def baseEnd_3369801 : Nat := 64086208259321310066299

theorem tailTrace_3369801 : CollatzResearch.WordTrace tailWord_3369801 prefixEnd_3369801 64086208259321310066299 := by
  unfold tailWord_3369801
  simp only [CollatzResearch.WordTrace]
  refine ⟨122906739664793968036725257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81937826443195978691150171 122906739664793968036725257)
  ·
    refine ⟨92180054748595476027543943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122906739664793968036725257 92180054748595476027543943)
    ·
      refine ⟨138270082122893214041315915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92180054748595476027543943 138270082122893214041315915)
      ·
        refine ⟨207405123184339821061973873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138270082122893214041315915 207405123184339821061973873)
        ·
          refine ⟨155553842388254865796480405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207405123184339821061973873 155553842388254865796480405)
          ·
            refine ⟨7291586361949446834210019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155553842388254865796480405 7291586361949446834210019)
            ·
              refine ⟨10937379542924170251315029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291586361949446834210019 10937379542924170251315029)
              ·
                refine ⟨64086208259321310066299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10937379542924170251315029 64086208259321310066299)
                ·
                  rfl

theorem cell23_3369801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 1, 9].length) (baseStart_3369801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369801 prefixEnd_3369801 := by exact prefixLift 3369801
  have htrace : WordTrace (prefixWord ++ tailWord_3369801) baseStart_3369801 baseEnd_3369801 := by
    simpa [prefixWord, tailWord_3369801, baseEnd_3369801] using wordTrace_append hprefix tailTrace_3369801
  have hstable : (prefixWord ++ tailWord_3369801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369801).length < 2 ^ (prefixWord ++ tailWord_3369801).sum := by decide
  have hdescent : baseEnd_3369801 < baseStart_3369801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369815 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_3369815 : Nat := 118140960795 + 3369815 * 2 ^ 59
def prefixEnd_3369815 : Nat := 4983230072969 + 3 ^ 40 * 3369815 * 2
def baseEnd_3369815 : Nat := 1730334811730838317015009

theorem tailTrace_3369815 : CollatzResearch.WordTrace tailWord_3369815 prefixEnd_3369815 1730334811730838317015009 := by
  unfold tailWord_3369815
  simp only [CollatzResearch.WordTrace]
  refine ⟨122907250286743248427734899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81938166857828832285156599 122907250286743248427734899)
  ·
    refine ⟨184360875430114872641602349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122907250286743248427734899 184360875430114872641602349)
    ·
      refine ⟨69135328286293077240600881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184360875430114872641602349 69135328286293077240600881)
      ·
        refine ⟨51851496214719807930450661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69135328286293077240600881 51851496214719807930450661)
        ·
          refine ⟨9722155540259963986959499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51851496214719807930450661 9722155540259963986959499)
          ·
            refine ⟨14583233310389945980439249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9722155540259963986959499 14583233310389945980439249)
            ·
              refine ⟨10937424982792459485329437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14583233310389945980439249 10937424982792459485329437)
              ·
                refine ⟨4101534368547172306998539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10937424982792459485329437 4101534368547172306998539)
                ·
                  refine ⟨6152301552820758460497809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101534368547172306998539 6152301552820758460497809)
                  ·
                    refine ⟨4614226164615568845373357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152301552820758460497809 4614226164615568845373357)
                    ·
                      refine ⟨1730334811730838317015009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4614226164615568845373357 1730334811730838317015009)
                      ·
                        rfl

theorem cell23_3369815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_3369815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369815 prefixEnd_3369815 := by exact prefixLift 3369815
  have htrace : WordTrace (prefixWord ++ tailWord_3369815) baseStart_3369815 baseEnd_3369815 := by
    simpa [prefixWord, tailWord_3369815, baseEnd_3369815] using wordTrace_append hprefix tailTrace_3369815
  have hstable : (prefixWord ++ tailWord_3369815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369815).length < 2 ^ (prefixWord ++ tailWord_3369815).sum := by decide
  have hdescent : baseEnd_3369815 < baseStart_3369815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369881 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 6]
def baseStart_3369881 : Nat := 118140960795 + 3369881 * 2 ^ 59
def prefixEnd_3369881 : Nat := 4983230072969 + 3 ^ 40 * 3369881 * 2
def baseEnd_3369881 : Nat := 1730368701454035058789705

theorem tailTrace_3369881 : CollatzResearch.WordTrace tailWord_3369881 prefixEnd_3369881 1730368701454035058789705 := by
  unfold tailWord_3369881
  simp only [CollatzResearch.WordTrace]
  refine ⟨122909657504504141699637497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81939771669669427799758331 122909657504504141699637497)
  ·
    refine ⟨92182243128378106274728123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122909657504504141699637497 92182243128378106274728123)
    ·
      refine ⟨138273364692567159412092185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92182243128378106274728123 138273364692567159412092185)
      ·
        refine ⟨103705023519425369559069139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138273364692567159412092185 103705023519425369559069139)
        ·
          refine ⟨155557535279138054338603709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103705023519425369559069139 155557535279138054338603709)
          ·
            refine ⟨58334075729676770376976391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155557535279138054338603709 58334075729676770376976391)
            ·
              refine ⟨87501113594515155565464587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58334075729676770376976391 87501113594515155565464587)
              ·
                refine ⟨131251670391772733348196881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87501113594515155565464587 131251670391772733348196881)
                ·
                  refine ⟨98438752793829550011147661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131251670391772733348196881 98438752793829550011147661)
                  ·
                    refine ⟨36914532297686081254180373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 98438752793829550011147661 36914532297686081254180373)
                    ·
                      refine ⟨1730368701454035058789705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36914532297686081254180373 1730368701454035058789705)
                      ·
                        rfl

theorem cell23_3369881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 3, 6].length) (baseStart_3369881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369881 prefixEnd_3369881 := by exact prefixLift 3369881
  have htrace : WordTrace (prefixWord ++ tailWord_3369881) baseStart_3369881 baseEnd_3369881 := by
    simpa [prefixWord, tailWord_3369881, baseEnd_3369881] using wordTrace_append hprefix tailTrace_3369881
  have hstable : (prefixWord ++ tailWord_3369881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369881).length < 2 ^ (prefixWord ++ tailWord_3369881).sum := by decide
  have hdescent : baseEnd_3369881 < baseStart_3369881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369885 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 3, 4, 2]
def baseStart_3369885 : Nat := 118140960795 + 3369885 * 2 ^ 59
def prefixEnd_3369885 : Nat := 4983230072969 + 3 ^ 40 * 3369885 * 2
def baseEnd_3369885 : Nat := 1730370755376653043139687

theorem tailTrace_3369885 : CollatzResearch.WordTrace tailWord_3369885 prefixEnd_3369885 1730370755376653043139687 := by
  unfold tailWord_3369885
  simp only [CollatzResearch.WordTrace]
  refine ⟨122909803396489650382783109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81939868930993100255188739 122909803396489650382783109)
  ·
    refine ⟨23045588136841809446771833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122909803396489650382783109 23045588136841809446771833)
    ·
      refine ⟨17284191102631357085078875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23045588136841809446771833 17284191102631357085078875)
      ·
        refine ⟨25926286653947035627618313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17284191102631357085078875 25926286653947035627618313)
        ·
          refine ⟨19444714990460276720713735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25926286653947035627618313 19444714990460276720713735)
          ·
            refine ⟨29167072485690415081070603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19444714990460276720713735 29167072485690415081070603)
            ·
              refine ⟨43750608728535622621605905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29167072485690415081070603 43750608728535622621605905)
              ·
                refine ⟨32812956546401716966204429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43750608728535622621605905 32812956546401716966204429)
                ·
                  refine ⟨12304858704900643862326661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32812956546401716966204429 12304858704900643862326661)
                  ·
                    refine ⟨2307161007168870724186249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12304858704900643862326661 2307161007168870724186249)
                    ·
                      refine ⟨1730370755376653043139687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307161007168870724186249 1730370755376653043139687)
                      ·
                        rfl

theorem cell23_3369885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 4, 2].length) (baseStart_3369885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369885 prefixEnd_3369885 := by exact prefixLift 3369885
  have htrace : WordTrace (prefixWord ++ tailWord_3369885) baseStart_3369885 baseEnd_3369885 := by
    simpa [prefixWord, tailWord_3369885, baseEnd_3369885] using wordTrace_append hprefix tailTrace_3369885
  have hstable : (prefixWord ++ tailWord_3369885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369885).length < 2 ^ (prefixWord ++ tailWord_3369885).sum := by decide
  have hdescent : baseEnd_3369885 < baseStart_3369885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369888 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3]
def baseStart_3369888 : Nat := 118140960795 + 3369888 * 2 ^ 59
def prefixEnd_3369888 : Nat := 4983230072969 + 3 ^ 40 * 3369888 * 2
def baseEnd_3369888 : Nat := 1730372295818616531402173

theorem tailTrace_3369888 : CollatzResearch.WordTrace tailWord_3369888 prefixEnd_3369888 1730372295818616531402173 := by
  unfold tailWord_3369888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61454956407739390947571159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81939941876985854596761545 61454956407739390947571159)
  ·
    refine ⟨92182434611609086421356739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61454956407739390947571159 92182434611609086421356739)
    ·
      refine ⟨138273651917413629632035109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92182434611609086421356739 138273651917413629632035109)
      ·
        refine ⟨25926309734515055556006583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138273651917413629632035109 25926309734515055556006583)
        ·
          refine ⟨38889464601772583334009875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25926309734515055556006583 38889464601772583334009875)
          ·
            refine ⟨58334196902658875001014813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38889464601772583334009875 58334196902658875001014813)
            ·
              refine ⟨21875323838497078125380555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58334196902658875001014813 21875323838497078125380555)
              ·
                refine ⟨32812985757745617188070833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21875323838497078125380555 32812985757745617188070833)
                ·
                  refine ⟨24609739318309212891053125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32812985757745617188070833 24609739318309212891053125)
                  ·
                    refine ⟨4614326122182977417072461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24609739318309212891053125 4614326122182977417072461)
                    ·
                      refine ⟨1730372295818616531402173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4614326122182977417072461 1730372295818616531402173)
                      ·
                        rfl

theorem cell23_3369888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_3369888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369888 prefixEnd_3369888 := by exact prefixLift 3369888
  have htrace : WordTrace (prefixWord ++ tailWord_3369888) baseStart_3369888 baseEnd_3369888 := by
    simpa [prefixWord, tailWord_3369888, baseEnd_3369888] using wordTrace_append hprefix tailTrace_3369888
  have hstable : (prefixWord ++ tailWord_3369888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369888).length < 2 ^ (prefixWord ++ tailWord_3369888).sum := by decide
  have hdescent : baseEnd_3369888 < baseStart_3369888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369895 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 2, 6]
def baseStart_3369895 : Nat := 118140960795 + 3369895 * 2 ^ 59
def prefixEnd_3369895 : Nat := 4983230072969 + 3 ^ 40 * 3369895 * 2
def baseEnd_3369895 : Nat := 576791963394399334671547

theorem tailTrace_3369895 : CollatzResearch.WordTrace tailWord_3369895 prefixEnd_3369895 576791963394399334671547 := by
  unfold tailWord_3369895
  simp only [CollatzResearch.WordTrace]
  refine ⟨122910168126453422090647139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81940112084302281393764759 122910168126453422090647139)
  ·
    refine ⟨184365252189680133135970709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122910168126453422090647139 184365252189680133135970709)
    ·
      refine ⟨8642121196391256240748627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 184365252189680133135970709 8642121196391256240748627)
      ·
        refine ⟨12963181794586884361122941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8642121196391256240748627 12963181794586884361122941)
        ·
          refine ⟨4861193172970081635421103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12963181794586884361122941 4861193172970081635421103)
          ·
            refine ⟨7291789759455122453131655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861193172970081635421103 7291789759455122453131655)
            ·
              refine ⟨10937684639182683679697483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7291789759455122453131655 10937684639182683679697483)
              ·
                refine ⟨16406526958774025519546225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10937684639182683679697483 16406526958774025519546225)
                ·
                  refine ⟨12304895219080519139659669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16406526958774025519546225 12304895219080519139659669)
                  ·
                    refine ⟨576791963394399334671547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12304895219080519139659669 576791963394399334671547)
                    ·
                      rfl

theorem cell23_3369895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_3369895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369895 prefixEnd_3369895 := by exact prefixLift 3369895
  have htrace : WordTrace (prefixWord ++ tailWord_3369895) baseStart_3369895 baseEnd_3369895 := by
    simpa [prefixWord, tailWord_3369895, baseEnd_3369895] using wordTrace_append hprefix tailTrace_3369895
  have hstable : (prefixWord ++ tailWord_3369895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369895).length < 2 ^ (prefixWord ++ tailWord_3369895).sum := by decide
  have hdescent : baseEnd_3369895 < baseStart_3369895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369942 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 7]
def baseStart_3369942 : Nat := 118140960795 + 3369942 * 2 ^ 59
def prefixEnd_3369942 : Nat := 4983230072969 + 3 ^ 40 * 3369942 * 2
def baseEnd_3369942 : Nat := 192266669308217702236325

theorem tailTrace_3369942 : CollatzResearch.WordTrace tailWord_3369942 prefixEnd_3369942 192266669308217702236325 := by
  unfold tailWord_3369942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7681992647330196819850505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81941254904855432745072053 7681992647330196819850505)
  ·
    refine ⟨5761494485497647614887879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7681992647330196819850505 5761494485497647614887879)
    ·
      refine ⟨8642241728246471422331819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5761494485497647614887879 8642241728246471422331819)
      ·
        refine ⟨12963362592369707133497729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8642241728246471422331819 12963362592369707133497729)
        ·
          refine ⟨9722521944277280350123297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12963362592369707133497729 9722521944277280350123297)
          ·
            refine ⟨7291891458207960262592473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9722521944277280350123297 7291891458207960262592473)
            ·
              refine ⟨5468918593655970196944355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7291891458207960262592473 5468918593655970196944355)
              ·
                refine ⟨8203377890483955295416533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5468918593655970196944355 8203377890483955295416533)
                ·
                  refine ⟨192266669308217702236325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8203377890483955295416533 192266669308217702236325)
                  ·
                    rfl

theorem cell23_3369942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_3369942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369942 prefixEnd_3369942 := by exact prefixLift 3369942
  have htrace : WordTrace (prefixWord ++ tailWord_3369942) baseStart_3369942 baseEnd_3369942 := by
    simpa [prefixWord, tailWord_3369942, baseEnd_3369942] using wordTrace_append hprefix tailTrace_3369942
  have hstable : (prefixWord ++ tailWord_3369942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369942).length < 2 ^ (prefixWord ++ tailWord_3369942).sum := by decide
  have hdescent : baseEnd_3369942 < baseStart_3369942 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3369995 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3]
def baseStart_3369995 : Nat := 118140960795 + 3369995 * 2 ^ 59
def prefixEnd_3369995 : Nat := 4983230072969 + 3 ^ 40 * 3369995 * 2
def baseEnd_3369995 : Nat := 1730427238248647612764181

theorem tailTrace_3369995 : CollatzResearch.WordTrace tailWord_3369995 prefixEnd_3369995 1730427238248647612764181 := by
  unfold tailWord_3369995
  simp only [CollatzResearch.WordTrace]
  refine ⟨122913815426091139169287439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81942543617394092779524959 122913815426091139169287439)
  ·
    refine ⟨184370723139136708753931159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122913815426091139169287439 184370723139136708753931159)
    ·
      refine ⟨276556084708705063130896739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184370723139136708753931159 276556084708705063130896739)
      ·
        refine ⟨414834127063057594696345109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276556084708705063130896739 414834127063057594696345109)
        ·
          refine ⟨19445349706080824751391177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 414834127063057594696345109 19445349706080824751391177)
          ·
            refine ⟨14584012279560618563543383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19445349706080824751391177 14584012279560618563543383)
            ·
              refine ⟨21876018419340927845315075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14584012279560618563543383 21876018419340927845315075)
              ·
                refine ⟨32814027629011391767972613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21876018419340927845315075 32814027629011391767972613)
                ·
                  refine ⟨6152630180439635956494865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32814027629011391767972613 6152630180439635956494865)
                  ·
                    refine ⟨4614472635329726967371149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6152630180439635956494865 4614472635329726967371149)
                    ·
                      refine ⟨1730427238248647612764181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4614472635329726967371149 1730427238248647612764181)
                      ·
                        rfl

theorem cell23_3369995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 3].length) (baseStart_3369995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3369995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3369995 prefixEnd_3369995 := by exact prefixLift 3369995
  have htrace : WordTrace (prefixWord ++ tailWord_3369995) baseStart_3369995 baseEnd_3369995 := by
    simpa [prefixWord, tailWord_3369995, baseEnd_3369995] using wordTrace_append hprefix tailTrace_3369995
  have hstable : (prefixWord ++ tailWord_3369995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3369995).length < 2 ^ (prefixWord ++ tailWord_3369995).sum := by decide
  have hdescent : baseEnd_3369995 < baseStart_3369995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3369995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370015 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 6]
def baseStart_3370015 : Nat := 118140960795 + 3370015 * 2 ^ 59
def prefixEnd_3370015 : Nat := 4983230072969 + 3 ^ 40 * 3370015 * 2
def baseEnd_3370015 : Nat := 192270834206859726057121

theorem tailTrace_3370015 : CollatzResearch.WordTrace tailWord_3370015 prefixEnd_3370015 192270834206859726057121 := by
  unfold tailWord_3370015
  simp only [CollatzResearch.WordTrace]
  refine ⟨122914544886018682585015499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81943029924012455056676999 122914544886018682585015499)
  ·
    refine ⟨184371817329028023877523249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122914544886018682585015499 184371817329028023877523249)
    ·
      refine ⟨138278862996771017908142437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184371817329028023877523249 138278862996771017908142437)
      ·
        refine ⟨25927286811894565857776707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138278862996771017908142437 25927286811894565857776707)
        ·
          refine ⟨38890930217841848786665061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25927286811894565857776707 38890930217841848786665061)
          ·
            refine ⟨7292049415845346647499699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38890930217841848786665061 7292049415845346647499699)
            ·
              refine ⟨10938074123768019971249549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7292049415845346647499699 10938074123768019971249549)
              ·
                refine ⟨4101777796413007489218581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10938074123768019971249549 4101777796413007489218581)
                ·
                  refine ⟨192270834206859726057121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4101777796413007489218581 192270834206859726057121)
                  ·
                    rfl

theorem cell23_3370015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 6].length) (baseStart_3370015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370015 prefixEnd_3370015 := by exact prefixLift 3370015
  have htrace : WordTrace (prefixWord ++ tailWord_3370015) baseStart_3370015 baseEnd_3370015 := by
    simpa [prefixWord, tailWord_3370015, baseEnd_3370015] using wordTrace_append hprefix tailTrace_3370015
  have hstable : (prefixWord ++ tailWord_3370015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370015).length < 2 ^ (prefixWord ++ tailWord_3370015).sum := by decide
  have hdescent : baseEnd_3370015 < baseStart_3370015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370065 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 4]
def baseStart_3370065 : Nat := 118140960795 + 3370065 * 2 ^ 59
def prefixEnd_3370065 : Nat := 4983230072969 + 3 ^ 40 * 3370065 * 2
def baseEnd_3370065 : Nat := 1730463181894462338888859

theorem tailTrace_3370065 : CollatzResearch.WordTrace tailWord_3370065 prefixEnd_3370065 1730463181894462338888859 := by
  unfold tailWord_3370065
  simp only [CollatzResearch.WordTrace]
  refine ⟨122916368535837541124335649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81944245690558360749557099 122916368535837541124335649)
  ·
    refine ⟨92187276401878155843251737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122916368535837541124335649 92187276401878155843251737)
    ·
      refine ⟨69140457301408616882438803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92187276401878155843251737 69140457301408616882438803)
      ·
        refine ⟨103710685952112925323658205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69140457301408616882438803 103710685952112925323658205)
        ·
          refine ⟨38891507232042346996371827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103710685952112925323658205 38891507232042346996371827)
          ·
            refine ⟨58337260848063520494557741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38891507232042346996371827 58337260848063520494557741)
            ·
              refine ⟨21876472818023820185459153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58337260848063520494557741 21876472818023820185459153)
              ·
                refine ⟨16407354613517865139094365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21876472818023820185459153 16407354613517865139094365)
                ·
                  refine ⟨6152757980069199427160387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16407354613517865139094365 6152757980069199427160387)
                  ·
                    refine ⟨9229136970103799140740581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6152757980069199427160387 9229136970103799140740581)
                    ·
                      refine ⟨1730463181894462338888859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9229136970103799140740581 1730463181894462338888859)
                      ·
                        rfl

theorem cell23_3370065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_3370065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370065 prefixEnd_3370065 := by exact prefixLift 3370065
  have htrace : WordTrace (prefixWord ++ tailWord_3370065) baseStart_3370065 baseEnd_3370065 := by
    simpa [prefixWord, tailWord_3370065, baseEnd_3370065] using wordTrace_append hprefix tailTrace_3370065
  have hstable : (prefixWord ++ tailWord_3370065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370065).length < 2 ^ (prefixWord ++ tailWord_3370065).sum := by decide
  have hdescent : baseEnd_3370065 < baseStart_3370065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370095 : List Nat := [1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4]
def baseStart_3370095 : Nat := 118140960795 + 3370095 * 2 ^ 59
def prefixEnd_3370095 : Nat := 4983230072969 + 3 ^ 40 * 3370095 * 2
def baseEnd_3370095 : Nat := 1730478586314097221513721

theorem tailTrace_3370095 : CollatzResearch.WordTrace tailWord_3370095 prefixEnd_3370095 1730478586314097221513721 := by
  unfold tailWord_3370095
  simp only [CollatzResearch.WordTrace]
  refine ⟨122917462725728856247927739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81944975150485904165285159 122917462725728856247927739)
  ·
    refine ⟨184376194088593284371891609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122917462725728856247927739 184376194088593284371891609)
    ·
      refine ⟨138282145566444963278918707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184376194088593284371891609 138282145566444963278918707)
      ·
        refine ⟨207423218349667444918378061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138282145566444963278918707 207423218349667444918378061)
        ·
          refine ⟨77783706881125291844391773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207423218349667444918378061 77783706881125291844391773)
          ·
            refine ⟨29168890080421984441646915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77783706881125291844391773 29168890080421984441646915)
            ·
              refine ⟨43753335120632976662470373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29168890080421984441646915 43753335120632976662470373)
              ·
                refine ⟨8203750335118683124213195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43753335120632976662470373 8203750335118683124213195)
                ·
                  refine ⟨12305625502678024686319793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8203750335118683124213195 12305625502678024686319793)
                  ·
                    refine ⟨9229219127008518514739845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12305625502678024686319793 9229219127008518514739845)
                    ·
                      refine ⟨1730478586314097221513721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9229219127008518514739845 1730478586314097221513721)
                      ·
                        rfl

theorem cell23_3370095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_3370095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370095 prefixEnd_3370095 := by exact prefixLift 3370095
  have htrace : WordTrace (prefixWord ++ tailWord_3370095) baseStart_3370095 baseEnd_3370095 := by
    simpa [prefixWord, tailWord_3370095, baseEnd_3370095] using wordTrace_append hprefix tailTrace_3370095
  have hstable : (prefixWord ++ tailWord_3370095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370095).length < 2 ^ (prefixWord ++ tailWord_3370095).sum := by decide
  have hdescent : baseEnd_3370095 < baseStart_3370095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370102 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_3370102 : Nat := 118140960795 + 3370102 * 2 ^ 59
def prefixEnd_3370102 : Nat := 4983230072969 + 3 ^ 40 * 3370102 * 2
def baseEnd_3370102 : Nat := 1730482180678678694126189

theorem tailTrace_3370102 : CollatzResearch.WordTrace tailWord_3370102 prefixEnd_3370102 1730482180678678694126189 := by
  unfold tailWord_3370102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7682357377293968527714535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81945145357802330962288373 7682357377293968527714535)
  ·
    refine ⟨11523536065940952791571803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7682357377293968527714535 11523536065940952791571803)
    ·
      refine ⟨17285304098911429187357705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11523536065940952791571803 17285304098911429187357705)
      ·
        refine ⟨12963978074183571890518279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17285304098911429187357705 12963978074183571890518279)
        ·
          refine ⟨19445967111275357835777419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12963978074183571890518279 19445967111275357835777419)
          ·
            refine ⟨29168950666913036753666129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19445967111275357835777419 29168950666913036753666129)
            ·
              refine ⟨21876713000184777565249597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29168950666913036753666129 21876713000184777565249597)
              ·
                refine ⟨8203767375069291586968599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21876713000184777565249597 8203767375069291586968599)
                ·
                  refine ⟨12305651062603937380452899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8203767375069291586968599 12305651062603937380452899)
                  ·
                    refine ⟨18458476593905906070679349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12305651062603937380452899 18458476593905906070679349)
                    ·
                      refine ⟨1730482180678678694126189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18458476593905906070679349 1730482180678678694126189)
                      ·
                        rfl

theorem cell23_3370102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_3370102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370102 prefixEnd_3370102 := by exact prefixLift 3370102
  have htrace : WordTrace (prefixWord ++ tailWord_3370102) baseStart_3370102 baseEnd_3370102 := by
    simpa [prefixWord, tailWord_3370102, baseEnd_3370102] using wordTrace_append hprefix tailTrace_3370102
  have hstable : (prefixWord ++ tailWord_3370102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370102).length < 2 ^ (prefixWord ++ tailWord_3370102).sum := by decide
  have hdescent : baseEnd_3370102 < baseStart_3370102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370105 : List Nat := [1, 2, 1, 3, 5, 1, 10]
def baseStart_3370105 : Nat := 118140960795 + 3370105 * 2 ^ 59
def prefixEnd_3370105 : Nat := 4983230072969 + 3 ^ 40 * 3370105 * 2
def baseEnd_3370105 : Nat := 21363996557044965214675

theorem tailTrace_3370105 : CollatzResearch.WordTrace tailWord_3370105 prefixEnd_3370105 21363996557044965214675 := by
  unfold tailWord_3370105
  simp only [CollatzResearch.WordTrace]
  refine ⟨122917827455692627955791769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81945218303795085303861179 122917827455692627955791769)
  ·
    refine ⟨92188370591769470966843827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122917827455692627955791769 92188370591769470966843827)
    ·
      refine ⟨138282555887654206450265741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92188370591769470966843827 138282555887654206450265741)
      ·
        refine ⟨51855958457870327418849653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138282555887654206450265741 51855958457870327418849653)
        ·
          refine ⟨4861496105425343195517155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51855958457870327418849653 4861496105425343195517155)
          ·
            refine ⟨7292244158138014793275733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861496105425343195517155 7292244158138014793275733)
            ·
              refine ⟨21363996557044965214675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7292244158138014793275733 21363996557044965214675)
              ·
                rfl

theorem cell23_3370105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 10].length) (baseStart_3370105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370105 prefixEnd_3370105 := by exact prefixLift 3370105
  have htrace : WordTrace (prefixWord ++ tailWord_3370105) baseStart_3370105 baseEnd_3370105 := by
    simpa [prefixWord, tailWord_3370105, baseEnd_3370105] using wordTrace_append hprefix tailTrace_3370105
  have hstable : (prefixWord ++ tailWord_3370105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370105).length < 2 ^ (prefixWord ++ tailWord_3370105).sum := by decide
  have hdescent : baseEnd_3370105 < baseStart_3370105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370110 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 3, 1, 3]
def baseStart_3370110 : Nat := 118140960795 + 3370110 * 2 ^ 59
def prefixEnd_3370110 : Nat := 4983230072969 + 3 ^ 40 * 3370110 * 2
def baseEnd_3370110 : Nat := 1730486288523914662826153

theorem tailTrace_3370110 : CollatzResearch.WordTrace tailWord_3370110 prefixEnd_3370110 1730486288523914662826153 := by
  unfold tailWord_3370110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364751227584314226215473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81945339880449675873149189 15364751227584314226215473)
  ·
    refine ⟨11523563420688235669661605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15364751227584314226215473 11523563420688235669661605)
    ·
      refine ⟨2160668141379044188061551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11523563420688235669661605 2160668141379044188061551)
      ·
        refine ⟨3241002212068566282092327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2160668141379044188061551 3241002212068566282092327)
        ·
          refine ⟨4861503318102849423138491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3241002212068566282092327 4861503318102849423138491)
          ·
            refine ⟨7292254977154274134707737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861503318102849423138491 7292254977154274134707737)
            ·
              refine ⟨5469191232865705601030803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7292254977154274134707737 5469191232865705601030803)
              ·
                refine ⟨8203786849298558401546205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469191232865705601030803 8203786849298558401546205)
                ·
                  refine ⟨3076420068486959400579827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8203786849298558401546205 3076420068486959400579827)
                  ·
                    refine ⟨4614630102730439100869741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3076420068486959400579827 4614630102730439100869741)
                    ·
                      refine ⟨1730486288523914662826153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4614630102730439100869741 1730486288523914662826153)
                      ·
                        rfl

theorem cell23_3370110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_3370110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370110 prefixEnd_3370110 := by exact prefixLift 3370110
  have htrace : WordTrace (prefixWord ++ tailWord_3370110) baseStart_3370110 baseEnd_3370110 := by
    simpa [prefixWord, tailWord_3370110, baseEnd_3370110] using wordTrace_append hprefix tailTrace_3370110
  have hstable : (prefixWord ++ tailWord_3370110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370110).length < 2 ^ (prefixWord ++ tailWord_3370110).sum := by decide
  have hdescent : baseEnd_3370110 < baseStart_3370110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370116 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 3, 2, 2]
def baseStart_3370116 : Nat := 118140960795 + 3370116 * 2 ^ 59
def prefixEnd_3370116 : Nat := 4983230072969 + 3 ^ 40 * 3370116 * 2
def baseEnd_3370116 : Nat := 1730489369407841639351125

theorem tailTrace_3370116 : CollatzResearch.WordTrace tailWord_3370116 prefixEnd_3370116 1730489369407841639351125 := by
  unfold tailWord_3370116
  simp only [CollatzResearch.WordTrace]
  refine ⟨61459114329326388417221101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81945485772435184556294801 61459114329326388417221101)
  ·
    refine ⟨23047167873497395656457913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61459114329326388417221101 23047167873497395656457913)
    ·
      refine ⟨17285375905123046742343435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23047167873497395656457913 17285375905123046742343435)
      ·
        refine ⟨25928063857684570113515153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17285375905123046742343435 25928063857684570113515153)
        ·
          refine ⟨19446047893263427585136365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25928063857684570113515153 19446047893263427585136365)
          ·
            refine ⟨7292267959973785344426137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19446047893263427585136365 7292267959973785344426137)
            ·
              refine ⟨5469200969980339008319603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7292267959973785344426137 5469200969980339008319603)
              ·
                refine ⟨8203801454970508512479405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469200969980339008319603 8203801454970508512479405)
                ·
                  refine ⟨3076425545613940692179777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8203801454970508512479405 3076425545613940692179777)
                  ·
                    refine ⟨2307319159210455519134833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3076425545613940692179777 2307319159210455519134833)
                    ·
                      refine ⟨1730489369407841639351125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307319159210455519134833 1730489369407841639351125)
                      ·
                        rfl

theorem cell23_3370116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 2, 2].length) (baseStart_3370116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370116 prefixEnd_3370116 := by exact prefixLift 3370116
  have htrace : WordTrace (prefixWord ++ tailWord_3370116) baseStart_3370116 baseEnd_3370116 := by
    simpa [prefixWord, tailWord_3370116, baseEnd_3370116] using wordTrace_append hprefix tailTrace_3370116
  have hstable : (prefixWord ++ tailWord_3370116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370116).length < 2 ^ (prefixWord ++ tailWord_3370116).sum := by decide
  have hdescent : baseEnd_3370116 < baseStart_3370116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370126 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 2, 4]
def baseStart_3370126 : Nat := 118140960795 + 3370126 * 2 ^ 59
def prefixEnd_3370126 : Nat := 4983230072969 + 3 ^ 40 * 3370126 * 2
def baseEnd_3370126 : Nat := 576831501404795533408693

theorem tailTrace_3370126 : CollatzResearch.WordTrace tailWord_3370126 prefixEnd_3370126 576831501404795533408693 := by
  unfold tailWord_3370126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15364824173577068567788279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81945728925744365694870821 15364824173577068567788279)
  ·
    refine ⟨23047236260365602851682419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15364824173577068567788279 23047236260365602851682419)
    ·
      refine ⟨34570854390548404277523629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23047236260365602851682419 34570854390548404277523629)
      ·
        refine ⟨12964070396455651604071361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34570854390548404277523629 12964070396455651604071361)
        ·
          refine ⟨9723052797341738703053521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12964070396455651604071361 9723052797341738703053521)
          ·
            refine ⟨7292289598006304027290141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9723052797341738703053521 7292289598006304027290141)
            ·
              refine ⟨2734608599252364010233803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7292289598006304027290141 2734608599252364010233803)
              ·
                refine ⟨4101912898878546015350705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2734608599252364010233803 4101912898878546015350705)
                ·
                  refine ⟨3076434674158909511513029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4101912898878546015350705 3076434674158909511513029)
                  ·
                    refine ⟨576831501404795533408693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076434674158909511513029 576831501404795533408693)
                    ·
                      rfl

theorem cell23_3370126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 2, 4].length) (baseStart_3370126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370126 prefixEnd_3370126 := by exact prefixLift 3370126
  have htrace : WordTrace (prefixWord ++ tailWord_3370126) baseStart_3370126 baseEnd_3370126 := by
    simpa [prefixWord, tailWord_3370126, baseEnd_3370126] using wordTrace_append hprefix tailTrace_3370126
  have hstable : (prefixWord ++ tailWord_3370126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370126).length < 2 ^ (prefixWord ++ tailWord_3370126).sum := by decide
  have hdescent : baseEnd_3370126 < baseStart_3370126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370145 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_3370145 : Nat := 118140960795 + 3370145 * 2 ^ 59
def prefixEnd_3370145 : Nat := 4983230072969 + 3 ^ 40 * 3370145 * 2
def baseEnd_3370145 : Nat := 1730504260346822025888491

theorem tailTrace_3370145 : CollatzResearch.WordTrace tailWord_3370145 prefixEnd_3370145 1730504260346822025888491 := by
  unfold tailWord_3370145
  simp only [CollatzResearch.WordTrace]
  refine ⟨122919286375547714787247889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81946190917031809858165259 122919286375547714787247889)
  ·
    refine ⟨92189464781660786090435917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122919286375547714787247889 92189464781660786090435917)
    ·
      refine ⟨34571049293122794783913469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92189464781660786090435917 34571049293122794783913469)
      ·
        refine ⟨12964143484921048043967551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34571049293122794783913469 12964143484921048043967551)
        ·
          refine ⟨19446215227381572065951327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12964143484921048043967551 19446215227381572065951327)
          ·
            refine ⟨29169322841072358098926991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19446215227381572065951327 29169322841072358098926991)
            ·
              refine ⟨43753984261608537148390487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29169322841072358098926991 43753984261608537148390487)
              ·
                refine ⟨65630976392412805722585731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43753984261608537148390487 65630976392412805722585731)
                ·
                  refine ⟨98446464588619208583878597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65630976392412805722585731 98446464588619208583878597)
                  ·
                    refine ⟨18458712110366101609477237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98446464588619208583878597 18458712110366101609477237)
                    ·
                      refine ⟨1730504260346822025888491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18458712110366101609477237 1730504260346822025888491)
                      ·
                        rfl

theorem cell23_3370145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_3370145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370145 prefixEnd_3370145 := by exact prefixLift 3370145
  have htrace : WordTrace (prefixWord ++ tailWord_3370145) baseStart_3370145 baseEnd_3370145 := by
    simpa [prefixWord, tailWord_3370145, baseEnd_3370145] using wordTrace_append hprefix tailTrace_3370145
  have hstable : (prefixWord ++ tailWord_3370145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370145).length < 2 ^ (prefixWord ++ tailWord_3370145).sum := by decide
  have hdescent : baseEnd_3370145 < baseStart_3370145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370159 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 1, 3, 2]
def baseStart_3370159 : Nat := 118140960795 + 3370159 * 2 ^ 59
def prefixEnd_3370159 : Nat := 4983230072969 + 3 ^ 40 * 3370159 * 2
def baseEnd_3370159 : Nat := 1730511449075984971113427

theorem tailTrace_3370159 : CollatzResearch.WordTrace tailWord_3370159 prefixEnd_3370159 1730511449075984971113427 := by
  unfold tailWord_3370159
  simp only [CollatzResearch.WordTrace]
  refine ⟨122919796997496995178257531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81946531331664663452171687 122919796997496995178257531)
  ·
    refine ⟨184379695496245492767386297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122919796997496995178257531 184379695496245492767386297)
    ·
      refine ⟨138284771622184119575539723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184379695496245492767386297 138284771622184119575539723)
      ·
        refine ⟨207427157433276179363309585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138284771622184119575539723 207427157433276179363309585)
        ·
          refine ⟨155570368074957134522482189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207427157433276179363309585 155570368074957134522482189)
          ·
            refine ⟨58338888028108925445930821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155570368074957134522482189 58338888028108925445930821)
            ·
              refine ⟨10938541505270423521112029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58338888028108925445930821 10938541505270423521112029)
              ·
                refine ⟨4101953064476408820417011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10938541505270423521112029 4101953064476408820417011)
                ·
                  refine ⟨6152929596714613230625517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4101953064476408820417011 6152929596714613230625517)
                  ·
                    refine ⟨2307348598767979961484569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6152929596714613230625517 2307348598767979961484569)
                    ·
                      refine ⟨1730511449075984971113427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307348598767979961484569 1730511449075984971113427)
                      ·
                        rfl

theorem cell23_3370159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3, 2].length) (baseStart_3370159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370159 prefixEnd_3370159 := by exact prefixLift 3370159
  have htrace : WordTrace (prefixWord ++ tailWord_3370159) baseStart_3370159 baseEnd_3370159 := by
    simpa [prefixWord, tailWord_3370159, baseEnd_3370159] using wordTrace_append hprefix tailTrace_3370159
  have hstable : (prefixWord ++ tailWord_3370159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370159).length < 2 ^ (prefixWord ++ tailWord_3370159).sum := by decide
  have hdescent : baseEnd_3370159 < baseStart_3370159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370185 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 4]
def baseStart_3370185 : Nat := 118140960795 + 3370185 * 2 ^ 59
def prefixEnd_3370185 : Nat := 4983230072969 + 3 ^ 40 * 3370185 * 2
def baseEnd_3370185 : Nat := 1730524799573001869388307

theorem tailTrace_3370185 : CollatzResearch.WordTrace tailWord_3370185 prefixEnd_3370185 1730524799573001869388307 := by
  unfold tailWord_3370185
  simp only [CollatzResearch.WordTrace]
  refine ⟨122920745295402801618704009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81947163530268534412469339 122920745295402801618704009)
  ·
    refine ⟨92190558971552101214028007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122920745295402801618704009 92190558971552101214028007)
    ·
      refine ⟨138285838457328151821042011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92190558971552101214028007 138285838457328151821042011)
      ·
        refine ⟨207428757685992227731563017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138285838457328151821042011 207428757685992227731563017)
        ·
          refine ⟨155571568264494170798672263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207428757685992227731563017 155571568264494170798672263)
          ·
            refine ⟨233357352396741256198008395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155571568264494170798672263 233357352396741256198008395)
            ·
              refine ⟨350036028595111884297012593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233357352396741256198008395 350036028595111884297012593)
              ·
                refine ⟨262527021446333913222759445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 350036028595111884297012593 262527021446333913222759445)
                ·
                  refine ⟨12305954130296902182316849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 262527021446333913222759445 12305954130296902182316849)
                  ·
                    refine ⟨9229465597722676636737637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12305954130296902182316849 9229465597722676636737637)
                    ·
                      refine ⟨1730524799573001869388307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9229465597722676636737637 1730524799573001869388307)
                      ·
                        rfl

theorem cell23_3370185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 6, 2, 4].length) (baseStart_3370185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370185 prefixEnd_3370185 := by exact prefixLift 3370185
  have htrace : WordTrace (prefixWord ++ tailWord_3370185) baseStart_3370185 baseEnd_3370185 := by
    simpa [prefixWord, tailWord_3370185, baseEnd_3370185] using wordTrace_append hprefix tailTrace_3370185
  have hstable : (prefixWord ++ tailWord_3370185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370185).length < 2 ^ (prefixWord ++ tailWord_3370185).sum := by decide
  have hdescent : baseEnd_3370185 < baseStart_3370185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370223 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 2, 2, 2]
def baseStart_3370223 : Nat := 118140960795 + 3370223 * 2 ^ 59
def prefixEnd_3370223 : Nat := 4983230072969 + 3 ^ 40 * 3370223 * 2
def baseEnd_3370223 : Nat := 1730544311837872720713133

theorem tailTrace_3370223 : CollatzResearch.WordTrace tailWord_3370223 prefixEnd_3370223 1730544311837872720713133 := by
  unfold tailWord_3370223
  simp only [CollatzResearch.WordTrace]
  refine ⟨122922131269265134108587323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81948087512843422739058215 122922131269265134108587323)
  ·
    refine ⟨184383196903897701162880985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122922131269265134108587323 184383196903897701162880985)
    ·
      refine ⟨138287397677923275872160739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184383196903897701162880985 138287397677923275872160739)
      ·
        refine ⟨207431096516884913808241109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138287397677923275872160739 207431096516884913808241109)
        ·
          refine ⟨4861666324614490167380651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 207431096516884913808241109 4861666324614490167380651)
          ·
            refine ⟨7292499486921735251070977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4861666324614490167380651 7292499486921735251070977)
            ·
              refine ⟨5469374615191301438303233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7292499486921735251070977 5469374615191301438303233)
              ·
                refine ⟨4102030961393476078727425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5469374615191301438303233 4102030961393476078727425)
                ·
                  refine ⟨3076523221045107059045569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4102030961393476078727425 3076523221045107059045569)
                  ·
                    refine ⟨2307392415783830294284177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3076523221045107059045569 2307392415783830294284177)
                    ·
                      refine ⟨1730544311837872720713133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307392415783830294284177 1730544311837872720713133)
                      ·
                        rfl

theorem cell23_3370223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 2, 2].length) (baseStart_3370223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370223 prefixEnd_3370223 := by exact prefixLift 3370223
  have htrace : WordTrace (prefixWord ++ tailWord_3370223) baseStart_3370223 baseEnd_3370223 := by
    simpa [prefixWord, tailWord_3370223, baseEnd_3370223] using wordTrace_append hprefix tailTrace_3370223
  have hstable : (prefixWord ++ tailWord_3370223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370223).length < 2 ^ (prefixWord ++ tailWord_3370223).sum := by decide
  have hdescent : baseEnd_3370223 < baseStart_3370223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370225 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_3370225 : Nat := 118140960795 + 3370225 * 2 ^ 59
def prefixEnd_3370225 : Nat := 4983230072969 + 3 ^ 40 * 3370225 * 2
def baseEnd_3370225 : Nat := 576848446266393904296041

theorem tailTrace_3370225 : CollatzResearch.WordTrace tailWord_3370225 prefixEnd_3370225 576848446266393904296041 := by
  unfold tailWord_3370225
  simp only [CollatzResearch.WordTrace]
  refine ⟨122922204215257888450160129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81948136143505258966773419 122922204215257888450160129)
  ·
    refine ⟨92191653161443416337620097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122922204215257888450160129 92191653161443416337620097)
    ·
      refine ⟨69143739871082562253215073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92191653161443416337620097 69143739871082562253215073)
      ·
        refine ⟨51857804903311921689911305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69143739871082562253215073 51857804903311921689911305)
        ·
          refine ⟨38893353677483941267433479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51857804903311921689911305 38893353677483941267433479)
          ·
            refine ⟨58340030516225911901150219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38893353677483941267433479 58340030516225911901150219)
            ·
              refine ⟨87510045774338867851725329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58340030516225911901150219 87510045774338867851725329)
              ·
                refine ⟨65632534330754150888793997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87510045774338867851725329 65632534330754150888793997)
                ·
                  refine ⟨24612200374032806583297749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65632534330754150888793997 24612200374032806583297749)
                  ·
                    refine ⟨576848446266393904296041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24612200374032806583297749 576848446266393904296041)
                    ·
                      rfl

theorem cell23_3370225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_3370225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370225 prefixEnd_3370225 := by exact prefixLift 3370225
  have htrace : WordTrace (prefixWord ++ tailWord_3370225) baseStart_3370225 baseEnd_3370225 := by
    simpa [prefixWord, tailWord_3370225, baseEnd_3370225] using wordTrace_append hprefix tailTrace_3370225
  have hstable : (prefixWord ++ tailWord_3370225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370225).length < 2 ^ (prefixWord ++ tailWord_3370225).sum := by decide
  have hdescent : baseEnd_3370225 < baseStart_3370225 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370289 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_3370289 : Nat := 118140960795 + 3370289 * 2 ^ 59
def prefixEnd_3370289 : Nat := 4983230072969 + 3 ^ 40 * 3370289 * 2
def baseEnd_3370289 : Nat := 576859400520356487495943

theorem tailTrace_3370289 : CollatzResearch.WordTrace tailWord_3370289 prefixEnd_3370289 576859400520356487495943 := by
  unfold tailWord_3370289
  simp only [CollatzResearch.WordTrace]
  refine ⟨122924538487026027380489921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81949692324684018253659947 122924538487026027380489921)
  ·
    refine ⟨92193403865269520535367441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122924538487026027380489921 92193403865269520535367441)
    ·
      refine ⟨69145052898952140401525581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92193403865269520535367441 69145052898952140401525581)
      ·
        refine ⟨25929394837107052650572093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69145052898952140401525581 25929394837107052650572093)
        ·
          refine ⟨9723523063915144743964535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25929394837107052650572093 9723523063915144743964535)
          ·
            refine ⟨14585284595872717115946803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723523063915144743964535 14585284595872717115946803)
            ·
              refine ⟨21877926893809075673920205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14585284595872717115946803 21877926893809075673920205)
              ·
                refine ⟨8204222585178403377720077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21877926893809075673920205 8204222585178403377720077)
                ·
                  refine ⟨3076583469441901266645029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8204222585178403377720077 3076583469441901266645029)
                  ·
                    refine ⟨576859400520356487495943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076583469441901266645029 576859400520356487495943)
                    ·
                      rfl

theorem cell23_3370289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_3370289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370289 prefixEnd_3370289 := by exact prefixLift 3370289
  have htrace : WordTrace (prefixWord ++ tailWord_3370289) baseStart_3370289 baseEnd_3370289 := by
    simpa [prefixWord, tailWord_3370289, baseEnd_3370289] using wordTrace_append hprefix tailTrace_3370289
  have hstable : (prefixWord ++ tailWord_3370289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370289).length < 2 ^ (prefixWord ++ tailWord_3370289).sum := by decide
  have hdescent : baseEnd_3370289 < baseStart_3370289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370312 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3]
def baseStart_3370312 : Nat := 118140960795 + 3370312 * 2 ^ 59
def prefixEnd_3370312 : Nat := 4983230072969 + 3 ^ 40 * 3370312 * 2
def baseEnd_3370312 : Nat := 1730590011616122872500223

theorem tailTrace_3370312 : CollatzResearch.WordTrace tailWord_3370312 prefixEnd_3370312 1730590011616122872500223 := by
  unfold tailWord_3370312
  simp only [CollatzResearch.WordTrace]
  refine ⟨61462688682971351154288595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81950251577295134872384793 61462688682971351154288595)
  ·
    refine ⟨92194033024457026731432893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61462688682971351154288595 92194033024457026731432893)
    ·
      refine ⟨34572762384171385024287335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92194033024457026731432893 34572762384171385024287335)
      ·
        refine ⟨51859143576257077536431003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34572762384171385024287335 51859143576257077536431003)
        ·
          refine ⟨77788715364385616304646505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51859143576257077536431003 77788715364385616304646505)
          ·
            refine ⟨58341536523289212228484879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77788715364385616304646505 58341536523289212228484879)
            ·
              refine ⟨87512304784933818342727319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58341536523289212228484879 87512304784933818342727319)
              ·
                refine ⟨131268457177400727514090979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87512304784933818342727319 131268457177400727514090979)
                ·
                  refine ⟨196902685766101091271136469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131268457177400727514090979 196902685766101091271136469)
                  ·
                    refine ⟨4614906697642994326667261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196902685766101091271136469 4614906697642994326667261)
                    ·
                      refine ⟨1730590011616122872500223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4614906697642994326667261 1730590011616122872500223)
                      ·
                        rfl

theorem cell23_3370312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_3370312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370312 prefixEnd_3370312 := by exact prefixLift 3370312
  have htrace : WordTrace (prefixWord ++ tailWord_3370312) baseStart_3370312 baseEnd_3370312 := by
    simpa [prefixWord, tailWord_3370312, baseEnd_3370312] using wordTrace_append hprefix tailTrace_3370312
  have hstable : (prefixWord ++ tailWord_3370312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370312).length < 2 ^ (prefixWord ++ tailWord_3370312).sum := by decide
  have hdescent : baseEnd_3370312 < baseStart_3370312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370329 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 3]
def baseStart_3370329 : Nat := 118140960795 + 3370329 * 2 ^ 59
def prefixEnd_3370329 : Nat := 4983230072969 + 3 ^ 40 * 3370329 * 2
def baseEnd_3370329 : Nat := 1730598740787249305987645

theorem tailTrace_3370329 : CollatzResearch.WordTrace tailWord_3370329 prefixEnd_3370329 1730598740787249305987645 := by
  unfold tailWord_3370329
  simp only [CollatzResearch.WordTrace]
  refine ⟨122925997406881114211946041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81950664937920742807964027 122925997406881114211946041)
  ·
    refine ⟨92194498055160835658959531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122925997406881114211946041 92194498055160835658959531)
    ·
      refine ⟨138291747082741253488439297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92194498055160835658959531 138291747082741253488439297)
      ·
        refine ⟨103718810312055940116329473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138291747082741253488439297 103718810312055940116329473)
        ·
          refine ⟨77789107734041955087247105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103718810312055940116329473 77789107734041955087247105)
          ·
            refine ⟨58341830800531466315435329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77789107734041955087247105 58341830800531466315435329)
            ·
              refine ⟨43756373100398599736576497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58341830800531466315435329 43756373100398599736576497)
              ·
                refine ⟨32817279825298949802432373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43756373100398599736576497 32817279825298949802432373)
                ·
                  refine ⟨3076619983621776543978035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32817279825298949802432373 3076619983621776543978035)
                  ·
                    refine ⟨4614929975432664815967053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3076619983621776543978035 4614929975432664815967053)
                    ·
                      refine ⟨1730598740787249305987645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4614929975432664815967053 1730598740787249305987645)
                      ·
                        rfl

theorem cell23_3370329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 1, 3].length) (baseStart_3370329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370329 prefixEnd_3370329 := by exact prefixLift 3370329
  have htrace : WordTrace (prefixWord ++ tailWord_3370329) baseStart_3370329 baseEnd_3370329 := by
    simpa [prefixWord, tailWord_3370329, baseEnd_3370329] using wordTrace_append hprefix tailTrace_3370329
  have hstable : (prefixWord ++ tailWord_3370329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370329).length < 2 ^ (prefixWord ++ tailWord_3370329).sum := by decide
  have hdescent : baseEnd_3370329 < baseStart_3370329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370389 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 5]
def baseStart_3370389 : Nat := 118140960795 + 3370389 * 2 ^ 59
def prefixEnd_3370389 : Nat := 4983230072969 + 3 ^ 40 * 3370389 * 2
def baseEnd_3370389 : Nat := 1730629549626519071237369

theorem tailTrace_3370389 : CollatzResearch.WordTrace tailWord_3370389 prefixEnd_3370389 1730629549626519071237369 := by
  unfold tailWord_3370389
  simp only [CollatzResearch.WordTrace]
  refine ⟨122928185786663744459130221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81952123857775829639420147 122928185786663744459130221)
  ·
    refine ⟨46098069669998904172173833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122928185786663744459130221 46098069669998904172173833)
    ·
      refine ⟨34573552252499178129130375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46098069669998904172173833 34573552252499178129130375)
      ·
        refine ⟨51860328378748767193695563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34573552252499178129130375 51860328378748767193695563)
        ·
          refine ⟨77790492568123150790543345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51860328378748767193695563 77790492568123150790543345)
          ·
            refine ⟨58342869426092363092907509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77790492568123150790543345 58342869426092363092907509)
            ·
              refine ⟨5469644008696159039960079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58342869426092363092907509 5469644008696159039960079)
              ·
                refine ⟨8204466013044238559940119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5469644008696159039960079 8204466013044238559940119)
                ·
                  refine ⟨12306699019566357839910179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204466013044238559940119 12306699019566357839910179)
                  ·
                    refine ⟨18460048529349536759865269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12306699019566357839910179 18460048529349536759865269)
                    ·
                      refine ⟨1730629549626519071237369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18460048529349536759865269 1730629549626519071237369)
                      ·
                        rfl

theorem cell23_3370389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_3370389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370389 prefixEnd_3370389 := by exact prefixLift 3370389
  have htrace : WordTrace (prefixWord ++ tailWord_3370389) baseStart_3370389 baseEnd_3370389 := by
    simpa [prefixWord, tailWord_3370389, baseEnd_3370389] using wordTrace_append hprefix tailTrace_3370389
  have hstable : (prefixWord ++ tailWord_3370389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370389).length < 2 ^ (prefixWord ++ tailWord_3370389).sum := by decide
  have hdescent : baseEnd_3370389 < baseStart_3370389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370392 : List Nat := [2, 1, 2, 5, 13]
def baseStart_3370392 : Nat := 118140960795 + 3370392 * 2 ^ 59
def prefixEnd_3370392 : Nat := 4983230072969 + 3 ^ 40 * 3370392 * 2
def baseEnd_3370392 : Nat := 2373979547419043291495

theorem tailTrace_3370392 : CollatzResearch.WordTrace tailWord_3370392 prefixEnd_3370392 2373979547419043291495 := by
  unfold tailWord_3370392
  simp only [CollatzResearch.WordTrace]
  refine ⟨61464147602826437985744715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81952196803768583980992953 61464147602826437985744715)
  ·
    refine ⟨92196221404239656978617073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61464147602826437985744715 92196221404239656978617073)
    ·
      refine ⟨69147166053179742733962805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92196221404239656978617073 69147166053179742733962805)
      ·
        refine ⟨6482546817485600881309013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69147166053179742733962805 6482546817485600881309013)
        ·
          refine ⟨2373979547419043291495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 6482546817485600881309013 2373979547419043291495)
          ·
            rfl

theorem cell23_3370392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 13].length) (baseStart_3370392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370392 prefixEnd_3370392 := by exact prefixLift 3370392
  have htrace : WordTrace (prefixWord ++ tailWord_3370392) baseStart_3370392 baseEnd_3370392 := by
    simpa [prefixWord, tailWord_3370392, baseEnd_3370392] using wordTrace_append hprefix tailTrace_3370392
  have hstable : (prefixWord ++ tailWord_3370392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370392).length < 2 ^ (prefixWord ++ tailWord_3370392).sum := by decide
  have hdescent : baseEnd_3370392 < baseStart_3370392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370397 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 1, 1, 3]
def baseStart_3370397 : Nat := 118140960795 + 3370397 * 2 ^ 59
def prefixEnd_3370397 : Nat := 4983230072969 + 3 ^ 40 * 3370397 * 2
def baseEnd_3370397 : Nat := 1730633657471755039937333

theorem tailTrace_3370397 : CollatzResearch.WordTrace tailWord_3370397 prefixEnd_3370397 1730633657471755039937333 := by
  unfold tailWord_3370397
  simp only [CollatzResearch.WordTrace]
  refine ⟨122928477570634761825421445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81952318380423174550280963 122928477570634761825421445)
  ·
    refine ⟨23049089544494017842266521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122928477570634761825421445 23049089544494017842266521)
    ·
      refine ⟨17286817158370513381699891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23049089544494017842266521 17286817158370513381699891)
      ·
        refine ⟨25930225737555770072549837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17286817158370513381699891 25930225737555770072549837)
        ·
          refine ⟨9723834651583413777206189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25930225737555770072549837 9723834651583413777206189)
          ·
            refine ⟨3646437994343780166452321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9723834651583413777206189 3646437994343780166452321)
            ·
              refine ⟨2734828495757835124839241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3646437994343780166452321 2734828495757835124839241)
              ·
                refine ⟨2051121371818376343629431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2734828495757835124839241 2051121371818376343629431)
                ·
                  refine ⟨3076682057727564515444147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051121371818376343629431 3076682057727564515444147)
                  ·
                    refine ⟨4615023086591346773166221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3076682057727564515444147 4615023086591346773166221)
                    ·
                      refine ⟨1730633657471755039937333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615023086591346773166221 1730633657471755039937333)
                      ·
                        rfl

theorem cell23_3370397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 1, 1, 3].length) (baseStart_3370397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370397 prefixEnd_3370397 := by exact prefixLift 3370397
  have htrace : WordTrace (prefixWord ++ tailWord_3370397) baseStart_3370397 baseEnd_3370397 := by
    simpa [prefixWord, tailWord_3370397, baseEnd_3370397] using wordTrace_append hprefix tailTrace_3370397
  have hstable : (prefixWord ++ tailWord_3370397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370397).length < 2 ^ (prefixWord ++ tailWord_3370397).sum := by decide
  have hdescent : baseEnd_3370397 < baseStart_3370397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370412 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 6]
def baseStart_3370412 : Nat := 118140960795 + 3370412 * 2 ^ 59
def prefixEnd_3370412 : Nat := 4983230072969 + 3 ^ 40 * 3370412 * 2
def baseEnd_3370412 : Nat := 1730641359681572481249763

theorem tailTrace_3370412 : CollatzResearch.WordTrace tailWord_3370412 prefixEnd_3370412 1730641359681572481249763 := by
  unfold tailWord_3370412
  simp only [CollatzResearch.WordTrace]
  refine ⟨61464512332790209693608745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81952683110386946258144993 61464512332790209693608745)
  ·
    refine ⟨46098384249592657270206559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61464512332790209693608745 46098384249592657270206559)
    ·
      refine ⟨69147576374388985905309839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46098384249592657270206559 69147576374388985905309839)
      ·
        refine ⟨103721364561583478857964759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69147576374388985905309839 103721364561583478857964759)
        ·
          refine ⟨155582046842375218286947139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103721364561583478857964759 155582046842375218286947139)
          ·
            refine ⟨233373070263562827430420709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155582046842375218286947139 233373070263562827430420709)
            ·
              refine ⟨43757450674418030143203883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233373070263562827430420709 43757450674418030143203883)
              ·
                refine ⟨65636176011627045214805825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43757450674418030143203883 65636176011627045214805825)
                ·
                  refine ⟨49227132008720283911104369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65636176011627045214805825 49227132008720283911104369)
                  ·
                    refine ⟨36920349006540212933328277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49227132008720283911104369 36920349006540212933328277)
                    ·
                      refine ⟨1730641359681572481249763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36920349006540212933328277 1730641359681572481249763)
                      ·
                        rfl

theorem cell23_3370412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 6].length) (baseStart_3370412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370412 prefixEnd_3370412 := by exact prefixLift 3370412
  have htrace : WordTrace (prefixWord ++ tailWord_3370412) baseStart_3370412 baseEnd_3370412 := by
    simpa [prefixWord, tailWord_3370412, baseEnd_3370412] using wordTrace_append hprefix tailTrace_3370412
  have hstable : (prefixWord ++ tailWord_3370412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370412).length < 2 ^ (prefixWord ++ tailWord_3370412).sum := by decide
  have hdescent : baseEnd_3370412 < baseStart_3370412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370413 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3370413 : Nat := 118140960795 + 3370413 * 2 ^ 59
def prefixEnd_3370413 : Nat := 4983230072969 + 3 ^ 40 * 3370413 * 2
def baseEnd_3370413 : Nat := 576880624387408992445753

theorem tailTrace_3370413 : CollatzResearch.WordTrace tailWord_3370413 prefixEnd_3370413 576880624387408992445753 := by
  unfold tailWord_3370413
  simp only [CollatzResearch.WordTrace]
  refine ⟨122929061138576796558003893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81952707425717864372002595 122929061138576796558003893)
  ·
    refine ⟨11524599481741574677312865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122929061138576796558003893 11524599481741574677312865)
    ·
      refine ⟨8643449611306181007984649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11524599481741574677312865 8643449611306181007984649)
      ·
        refine ⟨6482587208479635755988487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8643449611306181007984649 6482587208479635755988487)
        ·
          refine ⟨9723880812719453633982731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6482587208479635755988487 9723880812719453633982731)
          ·
            refine ⟨14585821219079180450974097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9723880812719453633982731 14585821219079180450974097)
            ·
              refine ⟨10939365914309385338230573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14585821219079180450974097 10939365914309385338230573)
              ·
                refine ⟨4102262217866019501836465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10939365914309385338230573 4102262217866019501836465)
                ·
                  refine ⟨3076696663399514626377349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4102262217866019501836465 3076696663399514626377349)
                  ·
                    refine ⟨576880624387408992445753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3076696663399514626377349 576880624387408992445753)
                    ·
                      rfl

theorem cell23_3370413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3370413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370413 prefixEnd_3370413 := by exact prefixLift 3370413
  have htrace : WordTrace (prefixWord ++ tailWord_3370413) baseStart_3370413 baseEnd_3370413 := by
    simpa [prefixWord, tailWord_3370413, baseEnd_3370413] using wordTrace_append hprefix tailTrace_3370413
  have hstable : (prefixWord ++ tailWord_3370413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370413).length < 2 ^ (prefixWord ++ tailWord_3370413).sum := by decide
  have hdescent : baseEnd_3370413 < baseStart_3370413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370476 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 1, 4, 2]
def baseStart_3370476 : Nat := 118140960795 + 3370476 * 2 ^ 59
def prefixEnd_3370476 : Nat := 4983230072969 + 3 ^ 40 * 3370476 * 2
def baseEnd_3370476 : Nat := 1730674222443460230849469

theorem tailTrace_3370476 : CollatzResearch.WordTrace tailWord_3370476 prefixEnd_3370476 1730674222443460230849469 := by
  unfold tailWord_3370476
  simp only [CollatzResearch.WordTrace]
  refine ⟨61465679468674279158773641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81954239291565705545031521 61465679468674279158773641)
  ·
    refine ⟨46099259601505709369080231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61465679468674279158773641 46099259601505709369080231)
    ·
      refine ⟨69148889402258564053620347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46099259601505709369080231 69148889402258564053620347)
      ·
        refine ⟨103723334103387846080430521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69148889402258564053620347 103723334103387846080430521)
        ·
          refine ⟨77792500577540884560322891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103723334103387846080430521 77792500577540884560322891)
          ·
            refine ⟨116688750866311326840484337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77792500577540884560322891 116688750866311326840484337)
            ·
              refine ⟨87516563149733495130363253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116688750866311326840484337 87516563149733495130363253)
              ·
                refine ⟨8204677795287515168471555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87516563149733495130363253 8204677795287515168471555)
                ·
                  refine ⟨12307016692931272752707333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8204677795287515168471555 12307016692931272752707333)
                  ·
                    refine ⟨2307565629924613641132625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12307016692931272752707333 2307565629924613641132625)
                    ·
                      refine ⟨1730674222443460230849469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307565629924613641132625 1730674222443460230849469)
                      ·
                        rfl

theorem cell23_3370476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 4, 2].length) (baseStart_3370476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370476 prefixEnd_3370476 := by exact prefixLift 3370476
  have htrace : WordTrace (prefixWord ++ tailWord_3370476) baseStart_3370476 baseEnd_3370476 := by
    simpa [prefixWord, tailWord_3370476, baseEnd_3370476] using wordTrace_append hprefix tailTrace_3370476
  have hstable : (prefixWord ++ tailWord_3370476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370476).length < 2 ^ (prefixWord ++ tailWord_3370476).sum := by decide
  have hdescent : baseEnd_3370476 < baseStart_3370476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370479 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3]
def baseStart_3370479 : Nat := 118140960795 + 3370479 * 2 ^ 59
def prefixEnd_3370479 : Nat := 4983230072969 + 3 ^ 40 * 3370479 * 2
def baseEnd_3370479 : Nat := 1730675762885423719111955

theorem tailTrace_3370479 : CollatzResearch.WordTrace tailWord_3370479 prefixEnd_3370479 1730675762885423719111955 := by
  unfold tailWord_3370479
  simp only [CollatzResearch.WordTrace]
  refine ⟨122931468356337689829906491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81954312237558459886604327 122931468356337689829906491)
  ·
    refine ⟨184397202534506534744859737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122931468356337689829906491 184397202534506534744859737)
    ·
      refine ⟨138297901900879901058644803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184397202534506534744859737 138297901900879901058644803)
      ·
        refine ⟨207446852851319851587967205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138297901900879901058644803 207446852851319851587967205)
        ·
          refine ⟨38896284909622472172743851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207446852851319851587967205 38896284909622472172743851)
          ·
            refine ⟨58344427364433708259115777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38896284909622472172743851 58344427364433708259115777)
            ·
              refine ⟨43758320523325281194336833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58344427364433708259115777 43758320523325281194336833)
              ·
                refine ⟨32818740392493960895752625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43758320523325281194336833 32818740392493960895752625)
                ·
                  refine ⟨24614055294370470671814469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32818740392493960895752625 24614055294370470671814469)
                  ·
                    refine ⟨4615135367694463250965213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24614055294370470671814469 4615135367694463250965213)
                    ·
                      refine ⟨1730675762885423719111955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4615135367694463250965213 1730675762885423719111955)
                      ·
                        rfl

theorem cell23_3370479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_3370479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370479 prefixEnd_3370479 := by exact prefixLift 3370479
  have htrace : WordTrace (prefixWord ++ tailWord_3370479) baseStart_3370479 baseEnd_3370479 := by
    simpa [prefixWord, tailWord_3370479, baseEnd_3370479] using wordTrace_append hprefix tailTrace_3370479
  have hstable : (prefixWord ++ tailWord_3370479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370479).length < 2 ^ (prefixWord ++ tailWord_3370479).sum := by decide
  have hdescent : baseEnd_3370479 < baseStart_3370479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3370493 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 4, 2, 2]
def baseStart_3370493 : Nat := 118140960795 + 3370493 * 2 ^ 59
def prefixEnd_3370493 : Nat := 4983230072969 + 3 ^ 40 * 3370493 * 2
def baseEnd_3370493 : Nat := 1730682951614586664336891

theorem tailTrace_3370493 : CollatzResearch.WordTrace tailWord_3370493 prefixEnd_3370493 1730682951614586664336891 := by
  unfold tailWord_3370493
  simp only [CollatzResearch.WordTrace]
  refine ⟨122931978978286970220916133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81954652652191313480610755 122931978978286970220916133)
  ·
    refine ⟨23049746058428806916421775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122931978978286970220916133 23049746058428806916421775)
    ·
      refine ⟨34574619087643210374632663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23049746058428806916421775 34574619087643210374632663)
      ·
        refine ⟨51861928631464815561948995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34574619087643210374632663 51861928631464815561948995)
        ·
          refine ⟨77792892947197223342923493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51861928631464815561948995 77792892947197223342923493)
          ·
            refine ⟨14586167427599479376798155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77792892947197223342923493 14586167427599479376798155)
            ·
              refine ⟨21879251141399219065197233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14586167427599479376798155 21879251141399219065197233)
              ·
                refine ⟨16409438356049414298897925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21879251141399219065197233 16409438356049414298897925)
                ·
                  refine ⟨3076769691759265181043361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16409438356049414298897925 3076769691759265181043361)
                  ·
                    refine ⟨2307577268819448885782521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3076769691759265181043361 2307577268819448885782521)
                    ·
                      refine ⟨1730682951614586664336891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2307577268819448885782521 1730682951614586664336891)
                      ·
                        rfl

theorem cell23_3370493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 2, 2].length) (baseStart_3370493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3370493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3370493 prefixEnd_3370493 := by exact prefixLift 3370493
  have htrace : WordTrace (prefixWord ++ tailWord_3370493) baseStart_3370493 baseEnd_3370493 := by
    simpa [prefixWord, tailWord_3370493, baseEnd_3370493] using wordTrace_append hprefix tailTrace_3370493
  have hstable : (prefixWord ++ tailWord_3370493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3370493).length < 2 ^ (prefixWord ++ tailWord_3370493).sum := by decide
  have hdescent : baseEnd_3370493 < baseStart_3370493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3370493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
