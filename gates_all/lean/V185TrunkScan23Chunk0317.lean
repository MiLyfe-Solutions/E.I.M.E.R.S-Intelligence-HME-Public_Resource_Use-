import V185TrunkScan23Chunk0316

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1875095 : List Nat := [1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1875095 : Nat := 118140960795 + 1875095 * 2 ^ 59
def prefixEnd_1875095 : Nat := 4983230072969 + 3 ^ 40 * 1875095 * 2
def baseEnd_1875095 : Nat := 962825007842446415889101

theorem tailTrace_1875095 : CollatzResearch.WordTrace tailWord_1875095 prefixEnd_1875095 962825007842446415889101 := by
  unfold tailWord_1875095
  simp only [CollatzResearch.WordTrace]
  refine ⟨68390333141858530575442739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45593555427905687050295159 68390333141858530575442739)
  ·
    refine ⟨102585499712787795863164109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68390333141858530575442739 102585499712787795863164109)
    ·
      refine ⟨38469562392295423448686541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102585499712787795863164109 38469562392295423448686541)
      ·
        refine ⟨14426085897110783793257453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38469562392295423448686541 14426085897110783793257453)
        ·
          refine ⟨5409782211416543922471545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14426085897110783793257453 5409782211416543922471545)
          ·
            refine ⟨4057336658562407941853659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5409782211416543922471545 4057336658562407941853659)
            ·
              refine ⟨6086004987843611912780489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057336658562407941853659 6086004987843611912780489)
              ·
                refine ⟨4564503740882708934585367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086004987843611912780489 4564503740882708934585367)
                ·
                  refine ⟨6846755611324063401878051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564503740882708934585367 6846755611324063401878051)
                  ·
                    refine ⟨10270133416986095102817077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6846755611324063401878051 10270133416986095102817077)
                    ·
                      refine ⟨962825007842446415889101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10270133416986095102817077 962825007842446415889101)
                      ·
                        rfl

theorem cell23_1875095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1875095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875095 prefixEnd_1875095 := by exact prefixLift 1875095
  have htrace : WordTrace (prefixWord ++ tailWord_1875095) baseStart_1875095 baseEnd_1875095 := by
    simpa [prefixWord, tailWord_1875095, baseEnd_1875095] using wordTrace_append hprefix tailTrace_1875095
  have hstable : (prefixWord ++ tailWord_1875095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875095).length < 2 ^ (prefixWord ++ tailWord_1875095).sum := by decide
  have hdescent : baseEnd_1875095 < baseStart_1875095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875102 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_1875102 : Nat := 118140960795 + 1875102 * 2 ^ 59
def prefixEnd_1875102 : Nat := 4983230072969 + 3 ^ 40 * 1875102 * 2
def baseEnd_1875102 : Nat := 320942867402342629500523

theorem tailTrace_1875102 : CollatzResearch.WordTrace tailWord_1875102 prefixEnd_1875102 320942867402342629500523 := by
  unfold tailWord_1875102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548823556604146346368445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45593725635222113847298373 8548823556604146346368445)
  ·
    refine ⟨3205808833726554879888167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8548823556604146346368445 3205808833726554879888167)
    ·
      refine ⟨4808713250589832319832251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3205808833726554879888167 4808713250589832319832251)
      ·
        refine ⟨7213069875884748479748377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808713250589832319832251 7213069875884748479748377)
        ·
          refine ⟨5409802406913561359811283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213069875884748479748377 5409802406913561359811283)
          ·
            refine ⟨8114703610370342039716925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409802406913561359811283 8114703610370342039716925)
            ·
              refine ⟨3043013853888878264893847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8114703610370342039716925 3043013853888878264893847)
              ·
                refine ⟨4564520780833317397340771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043013853888878264893847 4564520780833317397340771)
                ·
                  refine ⟨6846781171249976096011157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4564520780833317397340771 6846781171249976096011157)
                  ·
                    refine ⟨320942867402342629500523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6846781171249976096011157 320942867402342629500523)
                    ·
                      rfl

theorem cell23_1875102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_1875102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875102 prefixEnd_1875102 := by exact prefixLift 1875102
  have htrace : WordTrace (prefixWord ++ tailWord_1875102) baseStart_1875102 baseEnd_1875102 := by
    simpa [prefixWord, tailWord_1875102, baseEnd_1875102] using wordTrace_append hprefix tailTrace_1875102
  have hstable : (prefixWord ++ tailWord_1875102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875102).length < 2 ^ (prefixWord ++ tailWord_1875102).sum := by decide
  have hdescent : baseEnd_1875102 < baseStart_1875102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875149 : List Nat := [1, 6, 2, 2, 1, 1, 2, 8]
def baseStart_1875149 : Nat := 118140960795 + 1875149 * 2 ^ 59
def prefixEnd_1875149 : Nat := 4983230072969 + 3 ^ 40 * 1875149 * 2
def baseEnd_1875149 : Nat := 35661212436955155726439

theorem tailTrace_1875149 : CollatzResearch.WordTrace tailWord_1875149 prefixEnd_1875149 35661212436955155726439 := by
  unfold tailWord_1875149
  simp only [CollatzResearch.WordTrace]
  refine ⟨68392302683662897797908501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45594868455775265198605667 68392302683662897797908501)
  ·
    refine ⟨3205889188296698334276961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68392302683662897797908501 3205889188296698334276961)
    ·
      refine ⟨2404416891222523750707721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3205889188296698334276961 2404416891222523750707721)
      ·
        refine ⟨1803312668416892813030791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2404416891222523750707721 1803312668416892813030791)
        ·
          refine ⟨2704969002625339219546187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803312668416892813030791 2704969002625339219546187)
          ·
            refine ⟨4057453503938008829319281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704969002625339219546187 4057453503938008829319281)
            ·
              refine ⟨3043090127953506621989461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057453503938008829319281 3043090127953506621989461)
              ·
                refine ⟨35661212436955155726439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3043090127953506621989461 35661212436955155726439)
                ·
                  rfl

theorem cell23_1875149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 8].length) (baseStart_1875149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875149 prefixEnd_1875149 := by exact prefixLift 1875149
  have htrace : WordTrace (prefixWord ++ tailWord_1875149) baseStart_1875149 baseEnd_1875149 := by
    simpa [prefixWord, tailWord_1875149, baseEnd_1875149] using wordTrace_append hprefix tailTrace_1875149
  have hstable : (prefixWord ++ tailWord_1875149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875149).length < 2 ^ (prefixWord ++ tailWord_1875149).sum := by decide
  have hdescent : baseEnd_1875149 < baseStart_1875149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875159 : List Nat := [1, 1, 3, 2, 1, 2, 6, 1, 2, 1, 3]
def baseStart_1875159 : Nat := 118140960795 + 1875159 * 2 ^ 59
def prefixEnd_1875159 : Nat := 4983230072969 + 3 ^ 40 * 1875159 * 2
def baseEnd_1875159 : Nat := 962857870604334165488807

theorem tailTrace_1875159 : CollatzResearch.WordTrace tailWord_1875159 prefixEnd_1875159 962857870604334165488807 := by
  unfold tailWord_1875159
  simp only [CollatzResearch.WordTrace]
  refine ⟨68392667413626669505772531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45595111609084446337181687 68392667413626669505772531)
  ·
    refine ⟨102589001120440004258658797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68392667413626669505772531 102589001120440004258658797)
    ·
      refine ⟨38470875420165001596997049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102589001120440004258658797 38470875420165001596997049)
      ·
        refine ⟨28853156565123751197747787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38470875420165001596997049 28853156565123751197747787)
        ·
          refine ⟨43279734847685626796621681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28853156565123751197747787 43279734847685626796621681)
          ·
            refine ⟨32459801135764220097466261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43279734847685626796621681 32459801135764220097466261)
            ·
              refine ⟨1521553178238947817068731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32459801135764220097466261 1521553178238947817068731)
              ·
                refine ⟨2282329767358421725603097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521553178238947817068731 2282329767358421725603097)
                ·
                  refine ⟨1711747325518816294202323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2282329767358421725603097 1711747325518816294202323)
                  ·
                    refine ⟨2567620988278224441303485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1711747325518816294202323 2567620988278224441303485)
                    ·
                      refine ⟨962857870604334165488807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567620988278224441303485 962857870604334165488807)
                      ·
                        rfl

theorem cell23_1875159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 6, 1, 2, 1, 3].length) (baseStart_1875159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875159 prefixEnd_1875159 := by exact prefixLift 1875159
  have htrace : WordTrace (prefixWord ++ tailWord_1875159) baseStart_1875159 baseEnd_1875159 := by
    simpa [prefixWord, tailWord_1875159, baseEnd_1875159] using wordTrace_append hprefix tailTrace_1875159
  have hstable : (prefixWord ++ tailWord_1875159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875159).length < 2 ^ (prefixWord ++ tailWord_1875159).sum := by decide
  have hdescent : baseEnd_1875159 < baseStart_1875159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875169 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_1875169 : Nat := 118140960795 + 1875169 * 2 ^ 59
def prefixEnd_1875169 : Nat := 4983230072969 + 3 ^ 40 * 1875169 * 2
def baseEnd_1875169 : Nat := 962863005410879126363761

theorem tailTrace_1875169 : CollatzResearch.WordTrace tailWord_1875169 prefixEnd_1875169 962863005410879126363761 := by
  unfold tailWord_1875169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68393032143590441213636561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45595354762393627475757707 68393032143590441213636561)
  ·
    refine ⟨51294774107692830910227421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68393032143590441213636561 51294774107692830910227421)
    ·
      refine ⟨19235540290384811591335283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51294774107692830910227421 19235540290384811591335283)
      ·
        refine ⟨28853310435577217387002925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19235540290384811591335283 28853310435577217387002925)
        ·
          refine ⟨10819991413341456520126097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28853310435577217387002925 10819991413341456520126097)
          ·
            refine ⟨8114993560006092390094573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10819991413341456520126097 8114993560006092390094573)
            ·
              refine ⟨3043122585002284646285465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8114993560006092390094573 3043122585002284646285465)
              ·
                refine ⟨2282341938751713484714099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043122585002284646285465 2282341938751713484714099)
                ·
                  refine ⟨3423512908127570227071149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282341938751713484714099 3423512908127570227071149)
                  ·
                    refine ⟨1283817340547838835151681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423512908127570227071149 1283817340547838835151681)
                    ·
                      refine ⟨962863005410879126363761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283817340547838835151681 962863005410879126363761)
                      ·
                        rfl

theorem cell23_1875169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_1875169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875169 prefixEnd_1875169 := by exact prefixLift 1875169
  have htrace : WordTrace (prefixWord ++ tailWord_1875169) baseStart_1875169 baseEnd_1875169 := by
    simpa [prefixWord, tailWord_1875169, baseEnd_1875169] using wordTrace_append hprefix tailTrace_1875169
  have hstable : (prefixWord ++ tailWord_1875169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875169).length < 2 ^ (prefixWord ++ tailWord_1875169).sum := by decide
  have hdescent : baseEnd_1875169 < baseStart_1875169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875182 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2]
def baseStart_1875182 : Nat := 118140960795 + 1875182 * 2 ^ 59
def prefixEnd_1875182 : Nat := 4983230072969 + 3 ^ 40 * 1875182 * 2
def baseEnd_1875182 : Nat := 962869680659387575501201

theorem tailTrace_1875182 : CollatzResearch.WordTrace tailWord_1875182 prefixEnd_1875182 962869680659387575501201 := by
  unfold tailWord_1875182
  simp only [CollatzResearch.WordTrace]
  refine ⟨8549188286567918054232475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45595670861695562955906533 8549188286567918054232475)
  ·
    refine ⟨12823782429851877081348713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8549188286567918054232475 12823782429851877081348713)
    ·
      refine ⟨9617836822388907811011535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12823782429851877081348713 9617836822388907811011535)
      ·
        refine ⟨14426755233583361716517303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617836822388907811011535 14426755233583361716517303)
        ·
          refine ⟨21640132850375042574775955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14426755233583361716517303 21640132850375042574775955)
          ·
            refine ⟨32460199275562563862163933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21640132850375042574775955 32460199275562563862163933)
            ·
              refine ⟨12172574728335961448311475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32460199275562563862163933 12172574728335961448311475)
              ·
                refine ⟨18258862092503942172467213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12172574728335961448311475 18258862092503942172467213)
                ·
                  refine ⟨6847073284688978314675205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18258862092503942172467213 6847073284688978314675205)
                  ·
                    refine ⟨1283826240879183434001601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6847073284688978314675205 1283826240879183434001601)
                    ·
                      refine ⟨962869680659387575501201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283826240879183434001601 962869680659387575501201)
                      ·
                        rfl

theorem cell23_1875182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_1875182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875182 prefixEnd_1875182 := by exact prefixLift 1875182
  have htrace : WordTrace (prefixWord ++ tailWord_1875182) baseStart_1875182 baseEnd_1875182 := by
    simpa [prefixWord, tailWord_1875182, baseEnd_1875182] using wordTrace_append hprefix tailTrace_1875182
  have hstable : (prefixWord ++ tailWord_1875182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875182).length < 2 ^ (prefixWord ++ tailWord_1875182).sum := by decide
  have hdescent : baseEnd_1875182 < baseStart_1875182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875199 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 2, 2, 2]
def baseStart_1875199 : Nat := 118140960795 + 1875199 * 2 ^ 59
def prefixEnd_1875199 : Nat := 4983230072969 + 3 ^ 40 * 1875199 * 2
def baseEnd_1875199 : Nat := 962878409830514008988623

theorem tailTrace_1875199 : CollatzResearch.WordTrace tailWord_1875199 prefixEnd_1875199 962878409830514008988623 := by
  unfold tailWord_1875199
  simp only [CollatzResearch.WordTrace]
  refine ⟨68394126333481756337228651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45596084222321170891485767 68394126333481756337228651)
  ·
    refine ⟨102591189500222634505842977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68394126333481756337228651 102591189500222634505842977)
    ·
      refine ⟨76943392125166975879382233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102591189500222634505842977 76943392125166975879382233)
      ·
        refine ⟨57707544093875231909536675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76943392125166975879382233 57707544093875231909536675)
        ·
          refine ⟨86561316140812847864305013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57707544093875231909536675 86561316140812847864305013)
          ·
            refine ⟨8115123388201204487278595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86561316140812847864305013 8115123388201204487278595)
            ·
              refine ⟨12172685082301806730917893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8115123388201204487278595 12172685082301806730917893)
              ·
                refine ⟨2282378452931588762047105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12172685082301806730917893 2282378452931588762047105)
                ·
                  refine ⟨1711783839698691571535329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2282378452931588762047105 1711783839698691571535329)
                  ·
                    refine ⟨1283837879774018678651497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1711783839698691571535329 1283837879774018678651497)
                    ·
                      refine ⟨962878409830514008988623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283837879774018678651497 962878409830514008988623)
                      ·
                        rfl

theorem cell23_1875199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 2, 2].length) (baseStart_1875199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875199 prefixEnd_1875199 := by exact prefixLift 1875199
  have htrace : WordTrace (prefixWord ++ tailWord_1875199) baseStart_1875199 baseEnd_1875199 := by
    simpa [prefixWord, tailWord_1875199, baseEnd_1875199] using wordTrace_append hprefix tailTrace_1875199
  have hstable : (prefixWord ++ tailWord_1875199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875199).length < 2 ^ (prefixWord ++ tailWord_1875199).sum := by decide
  have hdescent : baseEnd_1875199 < baseStart_1875199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875235 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 1, 7]
def baseStart_1875235 : Nat := 118140960795 + 1875235 * 2 ^ 59
def prefixEnd_1875235 : Nat := 4983230072969 + 3 ^ 40 * 1875235 * 2
def baseEnd_1875235 : Nat := 320965631711358622712819

theorem tailTrace_1875235 : CollatzResearch.WordTrace tailWord_1875235 prefixEnd_1875235 320965631711358622712819 := by
  unfold tailWord_1875235
  simp only [CollatzResearch.WordTrace]
  refine ⟨68395439361351334485539159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45596959574234222990359439 68395439361351334485539159)
  ·
    refine ⟨102593159042027001728308739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68395439361351334485539159 102593159042027001728308739)
    ·
      refine ⟨153889738563040502592463109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102593159042027001728308739 153889738563040502592463109)
      ·
        refine ⟨28854325980570094236086833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153889738563040502592463109 28854325980570094236086833)
        ·
          refine ⟨21640744485427570677065125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28854325980570094236086833 21640744485427570677065125)
          ·
            refine ⟨4057639591017669501949711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21640744485427570677065125 4057639591017669501949711)
            ·
              refine ⟨6086459386526504252924567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057639591017669501949711 6086459386526504252924567)
              ·
                refine ⟨9129689079789756379386851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6086459386526504252924567 9129689079789756379386851)
                ·
                  refine ⟨13694533619684634569080277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9129689079789756379386851 13694533619684634569080277)
                  ·
                    refine ⟨320965631711358622712819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13694533619684634569080277 320965631711358622712819)
                    ·
                      rfl

theorem cell23_1875235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 1, 7].length) (baseStart_1875235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875235 prefixEnd_1875235 := by exact prefixLift 1875235
  have htrace : WordTrace (prefixWord ++ tailWord_1875235) baseStart_1875235 baseEnd_1875235 := by
    simpa [prefixWord, tailWord_1875235, baseEnd_1875235] using wordTrace_append hprefix tailTrace_1875235
  have hstable : (prefixWord ++ tailWord_1875235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875235).length < 2 ^ (prefixWord ++ tailWord_1875235).sum := by decide
  have hdescent : baseEnd_1875235 < baseStart_1875235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875252 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_1875252 : Nat := 118140960795 + 1875252 * 2 ^ 59
def prefixEnd_1875252 : Nat := 4983230072969 + 3 ^ 40 * 1875252 * 2
def baseEnd_1875252 : Nat := 320968541435067433875293

theorem tailTrace_1875252 : CollatzResearch.WordTrace tailWord_1875252 prefixEnd_1875252 320968541435067433875293 := by
  unfold tailWord_1875252
  simp only [CollatzResearch.WordTrace]
  refine ⟨34198029701144873194454005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45597372934859830925938673 34198029701144873194454005)
  ·
    refine ⟨3206065284482331861980063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34198029701144873194454005 3206065284482331861980063)
    ·
      refine ⟨4809097926723497792970095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206065284482331861980063 4809097926723497792970095)
      ·
        refine ⟨7213646890085246689455143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809097926723497792970095 7213646890085246689455143)
        ·
          refine ⟨10820470335127870034182715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7213646890085246689455143 10820470335127870034182715)
          ·
            refine ⟨16230705502691805051274073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10820470335127870034182715 16230705502691805051274073)
            ·
              refine ⟨12173029127018853788455555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16230705502691805051274073 12173029127018853788455555)
              ·
                refine ⟨18259543690528280682683333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12173029127018853788455555 18259543690528280682683333)
                ·
                  refine ⟨3423664441974052628003125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18259543690528280682683333 3423664441974052628003125)
                  ·
                    refine ⟨320968541435067433875293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3423664441974052628003125 320968541435067433875293)
                    ·
                      rfl

theorem cell23_1875252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_1875252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875252 prefixEnd_1875252 := by exact prefixLift 1875252
  have htrace : WordTrace (prefixWord ++ tailWord_1875252) baseStart_1875252 baseEnd_1875252 := by
    simpa [prefixWord, tailWord_1875252, baseEnd_1875252] using wordTrace_append hprefix tailTrace_1875252
  have hstable : (prefixWord ++ tailWord_1875252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875252).length < 2 ^ (prefixWord ++ tailWord_1875252).sum := by decide
  have hdescent : baseEnd_1875252 < baseStart_1875252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875309 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1875309 : Nat := 118140960795 + 1875309 * 2 ^ 59
def prefixEnd_1875309 : Nat := 4983230072969 + 3 ^ 40 * 1875309 * 2
def baseEnd_1875309 : Nat := 962934892702508578613117

theorem tailTrace_1875309 : CollatzResearch.WordTrace tailWord_1875309 prefixEnd_1875309 962934892702508578613117 := by
  unfold tailWord_1875309
  simp only [CollatzResearch.WordTrace]
  refine ⟨68398138363083245123732981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45598758908722163415821987 68398138363083245123732981)
  ·
    refine ⟨6412325471539054230349967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68398138363083245123732981 6412325471539054230349967)
    ·
      refine ⟨9618488207308581345524951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6412325471539054230349967 9618488207308581345524951)
      ·
        refine ⟨14427732310962872018287427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9618488207308581345524951 14427732310962872018287427)
        ·
          refine ⟨21641598466444308027431141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427732310962872018287427 21641598466444308027431141)
          ·
            refine ⟨4057799712458307755143339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21641598466444308027431141 4057799712458307755143339)
            ·
              refine ⟨6086699568687461632715009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057799712458307755143339 6086699568687461632715009)
              ·
                refine ⟨4565024676515596224536257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6086699568687461632715009 4565024676515596224536257)
                ·
                  refine ⟨3423768507386697168402193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565024676515596224536257 3423768507386697168402193)
                  ·
                    refine ⟨2567826380540022876301645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423768507386697168402193 2567826380540022876301645)
                    ·
                      refine ⟨962934892702508578613117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567826380540022876301645 962934892702508578613117)
                      ·
                        rfl

theorem cell23_1875309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1875309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875309 prefixEnd_1875309 := by exact prefixLift 1875309
  have htrace : WordTrace (prefixWord ++ tailWord_1875309) baseStart_1875309 baseEnd_1875309 := by
    simpa [prefixWord, tailWord_1875309, baseEnd_1875309] using wordTrace_append hprefix tailTrace_1875309
  have hstable : (prefixWord ++ tailWord_1875309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875309).length < 2 ^ (prefixWord ++ tailWord_1875309).sum := by decide
  have hdescent : baseEnd_1875309 < baseStart_1875309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875329 : List Nat := [1, 2, 4, 3, 2, 1, 1, 3, 6]
def baseStart_1875329 : Nat := 118140960795 + 1875329 * 2 ^ 59
def prefixEnd_1875329 : Nat := 4983230072969 + 3 ^ 40 * 1875329 * 2
def baseEnd_1875329 : Nat := 106993906923955388929225

theorem tailTrace_1875329 : CollatzResearch.WordTrace tailWord_1875329 prefixEnd_1875329 106993906923955388929225 := by
  unfold tailWord_1875329
  simp only [CollatzResearch.WordTrace]
  refine ⟨68398867823010788539461041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45599245215340525692974027 68398867823010788539461041)
  ·
    refine ⟨51299150867258091404595781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68398867823010788539461041 51299150867258091404595781)
    ·
      refine ⟨9618590787610892138361709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51299150867258091404595781 9618590787610892138361709)
      ·
        refine ⟨3606971545354084551885641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9618590787610892138361709 3606971545354084551885641)
        ·
          refine ⟨2705228659015563413914231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606971545354084551885641 2705228659015563413914231)
          ·
            refine ⟨4057842988523345120871347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705228659015563413914231 4057842988523345120871347)
            ·
              refine ⟨6086764482785017681307021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057842988523345120871347 6086764482785017681307021)
              ·
                refine ⟨2282536681044381630490133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6086764482785017681307021 2282536681044381630490133)
                ·
                  refine ⟨106993906923955388929225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2282536681044381630490133 106993906923955388929225)
                  ·
                    rfl

theorem cell23_1875329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 3, 6].length) (baseStart_1875329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875329 prefixEnd_1875329 := by exact prefixLift 1875329
  have htrace : WordTrace (prefixWord ++ tailWord_1875329) baseStart_1875329 baseEnd_1875329 := by
    simpa [prefixWord, tailWord_1875329, baseEnd_1875329] using wordTrace_append hprefix tailTrace_1875329
  have hstable : (prefixWord ++ tailWord_1875329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875329).length < 2 ^ (prefixWord ++ tailWord_1875329).sum := by decide
  have hdescent : baseEnd_1875329 < baseStart_1875329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875345 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 4]
def baseStart_1875345 : Nat := 118140960795 + 1875345 * 2 ^ 59
def prefixEnd_1875345 : Nat := 4983230072969 + 3 ^ 40 * 1875345 * 2
def baseEnd_1875345 : Nat := 962953378006070437762951

theorem tailTrace_1875345 : CollatzResearch.WordTrace tailWord_1875345 prefixEnd_1875345 962953378006070437762951 := by
  unfold tailWord_1875345
  simp only [CollatzResearch.WordTrace]
  refine ⟨68399451390952823272043489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45599634260635215514695659 68399451390952823272043489)
  ·
    refine ⟨51299588543214617454032617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68399451390952823272043489 51299588543214617454032617)
    ·
      refine ⟨38474691407410963090524463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51299588543214617454032617 38474691407410963090524463)
      ·
        refine ⟨57712037111116444635786695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38474691407410963090524463 57712037111116444635786695)
        ·
          refine ⟨86568055666674666953680043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57712037111116444635786695 86568055666674666953680043)
          ·
            refine ⟨129852083500012000430520065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86568055666674666953680043 129852083500012000430520065)
            ·
              refine ⟨97389062625009000322890049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129852083500012000430520065 97389062625009000322890049)
              ·
                refine ⟨73041796968756750242167537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97389062625009000322890049 73041796968756750242167537)
                ·
                  refine ⟨54781347726567562681625653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73041796968756750242167537 54781347726567562681625653)
                  ·
                    refine ⟨5135751349365709001402405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54781347726567562681625653 5135751349365709001402405)
                    ·
                      refine ⟨962953378006070437762951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5135751349365709001402405 962953378006070437762951)
                      ·
                        rfl

theorem cell23_1875345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 4].length) (baseStart_1875345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875345 prefixEnd_1875345 := by exact prefixLift 1875345
  have htrace : WordTrace (prefixWord ++ tailWord_1875345) baseStart_1875345 baseEnd_1875345 := by
    simpa [prefixWord, tailWord_1875345, baseEnd_1875345] using wordTrace_append hprefix tailTrace_1875345
  have hstable : (prefixWord ++ tailWord_1875345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875345).length < 2 ^ (prefixWord ++ tailWord_1875345).sum := by decide
  have hdescent : baseEnd_1875345 < baseStart_1875345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875349 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_1875349 : Nat := 118140960795 + 1875349 * 2 ^ 59
def prefixEnd_1875349 : Nat := 4983230072969 + 3 ^ 40 * 1875349 * 2
def baseEnd_1875349 : Nat := 962955431928688422112933

theorem tailTrace_1875349 : CollatzResearch.WordTrace tailWord_1875349 prefixEnd_1875349 962955431928688422112933 := by
  unfold tailWord_1875349
  simp only [CollatzResearch.WordTrace]
  refine ⟨68399597282938331955189101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45599731521958887970126067 68399597282938331955189101)
  ·
    refine ⟨25649848981101874483195913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68399597282938331955189101 25649848981101874483195913)
    ·
      refine ⟨19237386735826405862396935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25649848981101874483195913 19237386735826405862396935)
      ·
        refine ⟨28856080103739608793595403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19237386735826405862396935 28856080103739608793595403)
        ·
          refine ⟨43284120155609413190393105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28856080103739608793595403 43284120155609413190393105)
          ·
            refine ⟨32463090116707059892794829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43284120155609413190393105 32463090116707059892794829)
            ·
              refine ⟨12173658793765147459798061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32463090116707059892794829 12173658793765147459798061)
              ·
                refine ⟨4565122047661930297424273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12173658793765147459798061 4565122047661930297424273)
                ·
                  refine ⟨3423841535746447723068205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565122047661930297424273 3423841535746447723068205)
                  ·
                    refine ⟨1283940575904917896150577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3423841535746447723068205 1283940575904917896150577)
                    ·
                      refine ⟨962955431928688422112933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283940575904917896150577 962955431928688422112933)
                      ·
                        rfl

theorem cell23_1875349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_1875349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875349 prefixEnd_1875349 := by exact prefixLift 1875349
  have htrace : WordTrace (prefixWord ++ tailWord_1875349) baseStart_1875349 baseEnd_1875349 := by
    simpa [prefixWord, tailWord_1875349, baseEnd_1875349] using wordTrace_append hprefix tailTrace_1875349
  have hstable : (prefixWord ++ tailWord_1875349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875349).length < 2 ^ (prefixWord ++ tailWord_1875349).sum := by decide
  have hdescent : baseEnd_1875349 < baseStart_1875349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875372 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 4, 4]
def baseStart_1875372 : Nat := 118140960795 + 1875372 * 2 ^ 59
def prefixEnd_1875372 : Nat := 4983230072969 + 3 ^ 40 * 1875372 * 2
def baseEnd_1875372 : Nat := 320989080661247277375109

theorem tailTrace_1875372 : CollatzResearch.WordTrace tailWord_1875372 prefixEnd_1875372 320989080661247277375109 := by
  unfold tailWord_1875372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34200218080927503441638185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45600290774570004588850913 34200218080927503441638185)
  ·
    refine ⟨25650163560695627581228639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34200218080927503441638185 25650163560695627581228639)
    ·
      refine ⟨38475245341043441371842959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25650163560695627581228639 38475245341043441371842959)
      ·
        refine ⟨57712868011565162057764439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38475245341043441371842959 57712868011565162057764439)
        ·
          refine ⟨86569302017347743086646659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57712868011565162057764439 86569302017347743086646659)
          ·
            refine ⟨129853953026021614629969989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86569302017347743086646659 129853953026021614629969989)
            ·
              refine ⟨24347616192379052743119373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 129853953026021614629969989 24347616192379052743119373)
              ·
                refine ⟨9130356072142144778669765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24347616192379052743119373 9130356072142144778669765)
                ·
                  refine ⟨1711941763526652146000581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9130356072142144778669765 1711941763526652146000581)
                  ·
                    refine ⟨320989080661247277375109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711941763526652146000581 320989080661247277375109)
                    ·
                      rfl

theorem cell23_1875372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 4].length) (baseStart_1875372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875372 prefixEnd_1875372 := by exact prefixLift 1875372
  have htrace : WordTrace (prefixWord ++ tailWord_1875372) baseStart_1875372 baseEnd_1875372 := by
    simpa [prefixWord, tailWord_1875372, baseEnd_1875372] using wordTrace_append hprefix tailTrace_1875372
  have hstable : (prefixWord ++ tailWord_1875372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875372).length < 2 ^ (prefixWord ++ tailWord_1875372).sum := by decide
  have hdescent : baseEnd_1875372 < baseStart_1875372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875375 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6]
def baseStart_1875375 : Nat := 118140960795 + 1875375 * 2 ^ 59
def prefixEnd_1875375 : Nat := 4983230072969 + 3 ^ 40 * 1875375 * 2
def baseEnd_1875375 : Nat := 962968782425705320387813

theorem tailTrace_1875375 : CollatzResearch.WordTrace tailWord_1875375 prefixEnd_1875375 962968782425705320387813 := by
  unfold tailWord_1875375
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400545580844138395635579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45600363720562758930423719 68400545580844138395635579)
  ·
    refine ⟨102600818371266207593453369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68400545580844138395635579 102600818371266207593453369)
    ·
      refine ⟨76950613778449655695090027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102600818371266207593453369 76950613778449655695090027)
      ·
        refine ⟨115425920667674483542635041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76950613778449655695090027 115425920667674483542635041)
        ·
          refine ⟨86569440500755862656976281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115425920667674483542635041 86569440500755862656976281)
          ·
            refine ⟨64927080375566896992732211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86569440500755862656976281 64927080375566896992732211)
            ·
              refine ⟨97390620563350345489098317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64927080375566896992732211 97390620563350345489098317)
              ·
                refine ⟨36521482711256379558411869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97390620563350345489098317 36521482711256379558411869)
                ·
                  refine ⟨13695556016721142334404451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36521482711256379558411869 13695556016721142334404451)
                  ·
                    refine ⟨20543334025081713501606677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13695556016721142334404451 20543334025081713501606677)
                    ·
                      refine ⟨962968782425705320387813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20543334025081713501606677 962968782425705320387813)
                      ·
                        rfl

theorem cell23_1875375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 6].length) (baseStart_1875375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875375 prefixEnd_1875375 := by exact prefixLift 1875375
  have htrace : WordTrace (prefixWord ++ tailWord_1875375) baseStart_1875375 baseEnd_1875375 := by
    simpa [prefixWord, tailWord_1875375, baseEnd_1875375] using wordTrace_append hprefix tailTrace_1875375
  have hstable : (prefixWord ++ tailWord_1875375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875375).length < 2 ^ (prefixWord ++ tailWord_1875375).sum := by decide
  have hdescent : baseEnd_1875375 < baseStart_1875375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875379 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 7, 2, 2]
def baseStart_1875379 : Nat := 118140960795 + 1875379 * 2 ^ 59
def prefixEnd_1875379 : Nat := 4983230072969 + 3 ^ 40 * 1875379 * 2
def baseEnd_1875379 : Nat := 962970836348323304737795

theorem tailTrace_1875379 : CollatzResearch.WordTrace tailWord_1875379 prefixEnd_1875379 962970836348323304737795 := by
  unfold tailWord_1875379
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400691472829647078781191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45600460981886431385854127 68400691472829647078781191)
  ·
    refine ⟨102601037209244470618171787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68400691472829647078781191 102601037209244470618171787)
    ·
      refine ⟨153901555813866705927257681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102601037209244470618171787 153901555813866705927257681)
      ·
        refine ⟨115426166860400029445443261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153901555813866705927257681 115426166860400029445443261)
        ·
          refine ⟨43284812572650011042041223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115426166860400029445443261 43284812572650011042041223)
          ·
            refine ⟨64927218858975016563061835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43284812572650011042041223 64927218858975016563061835)
            ·
              refine ⟨97390828288462524844592753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64927218858975016563061835 97390828288462524844592753)
              ·
                refine ⟨73043121216346893633444565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97390828288462524844592753 73043121216346893633444565)
                ·
                  refine ⟨1711948153508130319533857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73043121216346893633444565 1711948153508130319533857)
                  ·
                    refine ⟨1283961115131097739650393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1711948153508130319533857 1283961115131097739650393)
                    ·
                      refine ⟨962970836348323304737795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1283961115131097739650393 962970836348323304737795)
                      ·
                        rfl

theorem cell23_1875379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 2, 2].length) (baseStart_1875379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875379 prefixEnd_1875379 := by exact prefixLift 1875379
  have htrace : WordTrace (prefixWord ++ tailWord_1875379) baseStart_1875379 baseEnd_1875379 := by
    simpa [prefixWord, tailWord_1875379, baseEnd_1875379] using wordTrace_append hprefix tailTrace_1875379
  have hstable : (prefixWord ++ tailWord_1875379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875379).length < 2 ^ (prefixWord ++ tailWord_1875379).sum := by decide
  have hdescent : baseEnd_1875379 < baseStart_1875379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875389 : List Nat := [1, 4, 1, 2, 2, 1, 1, 5, 2, 4]
def baseStart_1875389 : Nat := 118140960795 + 1875389 * 2 ^ 59
def prefixEnd_1875389 : Nat := 4983230072969 + 3 ^ 40 * 1875389 * 2
def baseEnd_1875389 : Nat := 320991990384956088537583

theorem tailTrace_1875389 : CollatzResearch.WordTrace tailWord_1875389 prefixEnd_1875389 320991990384956088537583 := by
  unfold tailWord_1875389
  simp only [CollatzResearch.WordTrace]
  refine ⟨68401056202793418786645221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45600704135195612524430147 68401056202793418786645221)
  ·
    refine ⟨12825198038023766022495979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68401056202793418786645221 12825198038023766022495979)
    ·
      refine ⟨19237797057035649033743969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12825198038023766022495979 19237797057035649033743969)
      ·
        refine ⟨14428347792776736775307977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19237797057035649033743969 14428347792776736775307977)
        ·
          refine ⟨10821260844582552581480983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14428347792776736775307977 10821260844582552581480983)
          ·
            refine ⟨16231891266873828872221475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821260844582552581480983 16231891266873828872221475)
            ·
              refine ⟨24347836900310743308332213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16231891266873828872221475 24347836900310743308332213)
              ·
                refine ⟨2282609709404132185156145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24347836900310743308332213 2282609709404132185156145)
                ·
                  refine ⟨1711957282053099138867109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2282609709404132185156145 1711957282053099138867109)
                  ·
                    refine ⟨320991990384956088537583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1711957282053099138867109 320991990384956088537583)
                    ·
                      rfl

theorem cell23_1875389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 2, 4].length) (baseStart_1875389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875389 prefixEnd_1875389 := by exact prefixLift 1875389
  have htrace : WordTrace (prefixWord ++ tailWord_1875389) baseStart_1875389 baseEnd_1875389 := by
    simpa [prefixWord, tailWord_1875389, baseEnd_1875389] using wordTrace_append hprefix tailTrace_1875389
  have hstable : (prefixWord ++ tailWord_1875389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875389).length < 2 ^ (prefixWord ++ tailWord_1875389).sum := by decide
  have hdescent : baseEnd_1875389 < baseStart_1875389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875392 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4]
def baseStart_1875392 : Nat := 118140960795 + 1875392 * 2 ^ 59
def prefixEnd_1875392 : Nat := 4983230072969 + 3 ^ 40 * 1875392 * 2
def baseEnd_1875392 : Nat := 962977511596831753875235

theorem tailTrace_1875392 : CollatzResearch.WordTrace tailWord_1875392 prefixEnd_1875392 962977511596831753875235 := by
  unfold tailWord_1875392
  simp only [CollatzResearch.WordTrace]
  refine ⟨34200582810891275149502215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45600777081188366866002953 34200582810891275149502215)
  ·
    refine ⟨51300874216336912724253323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34200582810891275149502215 51300874216336912724253323)
    ·
      refine ⟨76951311324505369086379985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51300874216336912724253323 76951311324505369086379985)
      ·
        refine ⟨57713483493379026814784989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76951311324505369086379985 57713483493379026814784989)
        ·
          refine ⟨21642556310017135055544371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57713483493379026814784989 21642556310017135055544371)
          ·
            refine ⟨32463834465025702583316557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642556310017135055544371 32463834465025702583316557)
            ·
              refine ⟨12173937924384638468743709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32463834465025702583316557 12173937924384638468743709)
              ·
                refine ⟨4565226721644239425778891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12173937924384638468743709 4565226721644239425778891)
                ·
                  refine ⟨6847840082466359138668337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565226721644239425778891 6847840082466359138668337)
                  ·
                    refine ⟨5135880061849769354001253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6847840082466359138668337 5135880061849769354001253)
                    ·
                      refine ⟨962977511596831753875235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5135880061849769354001253 962977511596831753875235)
                      ·
                        rfl

theorem cell23_1875392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_1875392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875392 prefixEnd_1875392 := by exact prefixLift 1875392
  have htrace : WordTrace (prefixWord ++ tailWord_1875392) baseStart_1875392 baseEnd_1875392 := by
    simpa [prefixWord, tailWord_1875392, baseEnd_1875392] using wordTrace_append hprefix tailTrace_1875392
  have hstable : (prefixWord ++ tailWord_1875392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875392).length < 2 ^ (prefixWord ++ tailWord_1875392).sum := by decide
  have hdescent : baseEnd_1875392 < baseStart_1875392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875394 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1875394 : Nat := 118140960795 + 1875394 * 2 ^ 59
def prefixEnd_1875394 : Nat := 4983230072969 + 3 ^ 40 * 1875394 * 2
def baseEnd_1875394 : Nat := 962978538558140746050227

theorem tailTrace_1875394 : CollatzResearch.WordTrace tailWord_1875394 prefixEnd_1875394 962978538558140746050227 := by
  unfold tailWord_1875394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17100309641943826160144309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45600825711850203093718157 17100309641943826160144309)
  ·
    refine ⟨1603154028932233702513529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17100309641943826160144309 1603154028932233702513529)
    ·
      refine ⟨1202365521699175276885147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1603154028932233702513529 1202365521699175276885147)
      ·
        refine ⟨1803548282548762915327721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202365521699175276885147 1803548282548762915327721)
        ·
          refine ⟨1352661211911572186495791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1803548282548762915327721 1352661211911572186495791)
          ·
            refine ⟨2028991817867358279743687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352661211911572186495791 2028991817867358279743687)
            ·
              refine ⟨3043487726801037419615531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028991817867358279743687 3043487726801037419615531)
              ·
                refine ⟨4565231590201556129423297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043487726801037419615531 4565231590201556129423297)
                ·
                  refine ⟨3423923692651167097067473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565231590201556129423297 3423923692651167097067473)
                  ·
                    refine ⟨2567942769488375322800605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423923692651167097067473 2567942769488375322800605)
                    ·
                      refine ⟨962978538558140746050227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567942769488375322800605 962978538558140746050227)
                      ·
                        rfl

theorem cell23_1875394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1875394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875394 prefixEnd_1875394 := by exact prefixLift 1875394
  have htrace : WordTrace (prefixWord ++ tailWord_1875394) baseStart_1875394 baseEnd_1875394 := by
    simpa [prefixWord, tailWord_1875394, baseEnd_1875394] using wordTrace_append hprefix tailTrace_1875394
  have hstable : (prefixWord ++ tailWord_1875394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875394).length < 2 ^ (prefixWord ++ tailWord_1875394).sum := by decide
  have hdescent : baseEnd_1875394 < baseStart_1875394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875399 : List Nat := [1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_1875399 : Nat := 118140960795 + 1875399 * 2 ^ 59
def prefixEnd_1875399 : Nat := 4983230072969 + 3 ^ 40 * 1875399 * 2
def baseEnd_1875399 : Nat := 962981105961413226487703

theorem tailTrace_1875399 : CollatzResearch.WordTrace tailWord_1875399 prefixEnd_1875399 962981105961413226487703 := by
  unfold tailWord_1875399
  simp only [CollatzResearch.WordTrace]
  refine ⟨68401420932757190494509251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45600947288504793663006167 68401420932757190494509251)
  ·
    refine ⟨102602131399135785741763877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68401420932757190494509251 102602131399135785741763877)
    ·
      refine ⟨19237899637337959826580727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102602131399135785741763877 19237899637337959826580727)
      ·
        refine ⟨28856849456006939739871091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19237899637337959826580727 28856849456006939739871091)
        ·
          refine ⟨43285274184010409609806637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28856849456006939739871091 43285274184010409609806637)
          ·
            refine ⟨16231977819003903603677489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43285274184010409609806637 16231977819003903603677489)
            ·
              refine ⟨12173983364252927702758117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16231977819003903603677489 12173983364252927702758117)
              ·
                refine ⟨2282621880797423944267147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12173983364252927702758117 2282621880797423944267147)
                ·
                  refine ⟨3423932821196135916400721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282621880797423944267147 3423932821196135916400721)
                  ·
                    refine ⟨2567949615897101937300541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423932821196135916400721 2567949615897101937300541)
                    ·
                      refine ⟨962981105961413226487703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567949615897101937300541 962981105961413226487703)
                      ·
                        rfl

theorem cell23_1875399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_1875399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875399 prefixEnd_1875399 := by exact prefixLift 1875399
  have htrace : WordTrace (prefixWord ++ tailWord_1875399) baseStart_1875399 baseEnd_1875399 := by
    simpa [prefixWord, tailWord_1875399, baseEnd_1875399] using wordTrace_append hprefix tailTrace_1875399
  have hstable : (prefixWord ++ tailWord_1875399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875399).length < 2 ^ (prefixWord ++ tailWord_1875399).sum := by decide
  have hdescent : baseEnd_1875399 < baseStart_1875399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875416 : List Nat := [2, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_1875416 : Nat := 118140960795 + 1875416 * 2 ^ 59
def prefixEnd_1875416 : Nat := 4983230072969 + 3 ^ 40 * 1875416 * 2
def baseEnd_1875416 : Nat := 962989835132539659975125

theorem tailTrace_1875416 : CollatzResearch.WordTrace tailWord_1875416 prefixEnd_1875416 962989835132539659975125 := by
  unfold tailWord_1875416
  simp only [CollatzResearch.WordTrace]
  refine ⟨34201020486847801198939051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45601360649130401598585401 34201020486847801198939051)
  ·
    refine ⟨51301530730271701798408577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34201020486847801198939051 51301530730271701798408577)
    ·
      refine ⟨38476148047703776348806433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51301530730271701798408577 38476148047703776348806433)
      ·
        refine ⟨28857111035777832261604825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38476148047703776348806433 28857111035777832261604825)
        ·
          refine ⟨21642833276833374196203619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28857111035777832261604825 21642833276833374196203619)
          ·
            refine ⟨32464249915250061294305429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21642833276833374196203619 32464249915250061294305429)
            ·
              refine ⟨1521761714777346623170567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32464249915250061294305429 1521761714777346623170567)
              ·
                refine ⟨2282642572166019934755851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1521761714777346623170567 2282642572166019934755851)
                ·
                  refine ⟨3423963858249029902133777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2282642572166019934755851 3423963858249029902133777)
                  ·
                    refine ⟨2567972893686772426600333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3423963858249029902133777 2567972893686772426600333)
                    ·
                      refine ⟨962989835132539659975125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2567972893686772426600333 962989835132539659975125)
                      ·
                        rfl

theorem cell23_1875416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_1875416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875416 prefixEnd_1875416 := by exact prefixLift 1875416
  have htrace : WordTrace (prefixWord ++ tailWord_1875416) baseStart_1875416 baseEnd_1875416 := by
    simpa [prefixWord, tailWord_1875416, baseEnd_1875416] using wordTrace_append hprefix tailTrace_1875416
  have hstable : (prefixWord ++ tailWord_1875416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875416).length < 2 ^ (prefixWord ++ tailWord_1875416).sum := by decide
  have hdescent : baseEnd_1875416 < baseStart_1875416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875439 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 5, 3, 2]
def baseStart_1875439 : Nat := 118140960795 + 1875439 * 2 ^ 59
def prefixEnd_1875439 : Nat := 4983230072969 + 3 ^ 40 * 1875439 * 2
def baseEnd_1875439 : Nat := 963001645187593069987519

theorem tailTrace_1875439 : CollatzResearch.WordTrace tailWord_1875439 prefixEnd_1875439 963001645187593069987519 := by
  unfold tailWord_1875439
  simp only [CollatzResearch.WordTrace]
  refine ⟨68402879852612277325965371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45601919901741518217310247 68402879852612277325965371)
  ·
    refine ⟨102604319778918415988948057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68402879852612277325965371 102604319778918415988948057)
    ·
      refine ⟨76953239834188811991711043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102604319778918415988948057 76953239834188811991711043)
      ·
        refine ⟨115429859751283217987566565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76953239834188811991711043 115429859751283217987566565)
        ·
          refine ⟨21643098703365603372668731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115429859751283217987566565 21643098703365603372668731)
          ·
            refine ⟨32464648055048405059003097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21643098703365603372668731 32464648055048405059003097)
            ·
              refine ⟨24348486041286303794252323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32464648055048405059003097 24348486041286303794252323)
              ·
                refine ⟨36522729061929455691378485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24348486041286303794252323 36522729061929455691378485)
                ·
                  refine ⟨3424005849555886471066733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36522729061929455691378485 3424005849555886471066733)
                  ·
                    refine ⟨1284002193583457426650025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424005849555886471066733 1284002193583457426650025)
                    ·
                      refine ⟨963001645187593069987519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284002193583457426650025 963001645187593069987519)
                      ·
                        rfl

theorem cell23_1875439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 3, 2].length) (baseStart_1875439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875439 prefixEnd_1875439 := by exact prefixLift 1875439
  have htrace : WordTrace (prefixWord ++ tailWord_1875439) baseStart_1875439 baseEnd_1875439 := by
    simpa [prefixWord, tailWord_1875439, baseEnd_1875439] using wordTrace_append hprefix tailTrace_1875439
  have hstable : (prefixWord ++ tailWord_1875439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875439).length < 2 ^ (prefixWord ++ tailWord_1875439).sum := by decide
  have hdescent : baseEnd_1875439 < baseStart_1875439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875446 : List Nat := [5, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_1875446 : Nat := 118140960795 + 1875446 * 2 ^ 59
def prefixEnd_1875446 : Nat := 4983230072969 + 3 ^ 40 * 1875446 * 2
def baseEnd_1875446 : Nat := 963005239552174542599987

theorem tailTrace_1875446 : CollatzResearch.WordTrace tailWord_1875446 prefixEnd_1875446 963005239552174542599987 := by
  unfold tailWord_1875446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4275195947724182345091887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45602090109057945014313461 4275195947724182345091887)
  ·
    refine ⟨6412793921586273517637831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4275195947724182345091887 6412793921586273517637831)
    ·
      refine ⟨9619190882379410276456747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6412793921586273517637831 9619190882379410276456747)
      ·
        refine ⟨14428786323569115414685121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619190882379410276456747 14428786323569115414685121)
        ·
          refine ⟨10821589742676836561013841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14428786323569115414685121 10821589742676836561013841)
          ·
            refine ⟨8116192307007627420760381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10821589742676836561013841 8116192307007627420760381)
            ·
              refine ⟨3043572115127860282785143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8116192307007627420760381 3043572115127860282785143)
              ·
                refine ⟨4565358172691790424177715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043572115127860282785143 4565358172691790424177715)
                ·
                  refine ⟨6848037259037685636266573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4565358172691790424177715 6848037259037685636266573)
                  ·
                    refine ⟨2568013972139132113599965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6848037259037685636266573 2568013972139132113599965)
                    ·
                      refine ⟨963005239552174542599987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2568013972139132113599965 963005239552174542599987)
                      ·
                        rfl

theorem cell23_1875446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_1875446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875446 prefixEnd_1875446 := by exact prefixLift 1875446
  have htrace : WordTrace (prefixWord ++ tailWord_1875446) baseStart_1875446 baseEnd_1875446 := by
    simpa [prefixWord, tailWord_1875446, baseEnd_1875446] using wordTrace_append hprefix tailTrace_1875446
  have hstable : (prefixWord ++ tailWord_1875446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875446).length < 2 ^ (prefixWord ++ tailWord_1875446).sum := by decide
  have hdescent : baseEnd_1875446 < baseStart_1875446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875452 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1875452 : Nat := 118140960795 + 1875452 * 2 ^ 59
def prefixEnd_1875452 : Nat := 4983230072969 + 3 ^ 40 * 1875452 * 2
def baseEnd_1875452 : Nat := 963008320436101519124959

theorem tailTrace_1875452 : CollatzResearch.WordTrace tailWord_1875452 prefixEnd_1875452 963008320436101519124959 := by
  unfold tailWord_1875452
  simp only [CollatzResearch.WordTrace]
  refine ⟨34201677000782590273094305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45602236001043453697459073 34201677000782590273094305)
  ·
    refine ⟨25651257750586942704820729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34201677000782590273094305 25651257750586942704820729)
    ·
      refine ⟨19238443312940207028615547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25651257750586942704820729 19238443312940207028615547)
      ·
        refine ⟨28857664969410310542923321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19238443312940207028615547 28857664969410310542923321)
        ·
          refine ⟨21643248727057732907192491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28857664969410310542923321 21643248727057732907192491)
          ·
            refine ⟨32464873090586599360788737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21643248727057732907192491 32464873090586599360788737)
            ·
              refine ⟨24348654817939949520591553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32464873090586599360788737 24348654817939949520591553)
              ·
                refine ⟨18261491113454962140443665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24348654817939949520591553 18261491113454962140443665)
                ·
                  refine ⟨13696118335091221605332749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18261491113454962140443665 13696118335091221605332749)
                  ·
                    refine ⟨5136044375659208101999781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13696118335091221605332749 5136044375659208101999781)
                    ·
                      refine ⟨963008320436101519124959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5136044375659208101999781 963008320436101519124959)
                      ·
                        rfl

theorem cell23_1875452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1875452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875452 prefixEnd_1875452 := by exact prefixLift 1875452
  have htrace : WordTrace (prefixWord ++ tailWord_1875452) baseStart_1875452 baseEnd_1875452 := by
    simpa [prefixWord, tailWord_1875452, baseEnd_1875452] using wordTrace_append hprefix tailTrace_1875452
  have hstable : (prefixWord ++ tailWord_1875452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875452).length < 2 ^ (prefixWord ++ tailWord_1875452).sum := by decide
  have hdescent : baseEnd_1875452 < baseStart_1875452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875529 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 5, 2]
def baseStart_1875529 : Nat := 118140960795 + 1875529 * 2 ^ 59
def prefixEnd_1875529 : Nat := 4983230072969 + 3 ^ 40 * 1875529 * 2
def baseEnd_1875529 : Nat := 963047858446497717862105

theorem tailTrace_1875529 : CollatzResearch.WordTrace tailWord_1875529 prefixEnd_1875529 963047858446497717862105 := by
  unfold tailWord_1875529
  simp only [CollatzResearch.WordTrace]
  refine ⟨68406162422286222696741641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45604108281524148464494427 68406162422286222696741641)
  ·
    refine ⟨51304621816714667022556231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68406162422286222696741641 51304621816714667022556231)
    ·
      refine ⟨76956932725072000533834347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51304621816714667022556231 76956932725072000533834347)
      ·
        refine ⟨115435399087608000800751521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76956932725072000533834347 115435399087608000800751521)
        ·
          refine ⟨86576549315706000600563641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115435399087608000800751521 86576549315706000600563641)
          ·
            refine ⟨64932411986779500450422731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86576549315706000600563641 64932411986779500450422731)
            ·
              refine ⟨97398617980169250675634097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64932411986779500450422731 97398617980169250675634097)
              ·
                refine ⟨73048963485126938006725573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97398617980169250675634097 73048963485126938006725573)
                ·
                  refine ⟨13696680653461300876261045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73048963485126938006725573 13696680653461300876261045)
                  ·
                    refine ⟨1284063811261996957149473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13696680653461300876261045 1284063811261996957149473)
                    ·
                      refine ⟨963047858446497717862105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284063811261996957149473 963047858446497717862105)
                      ·
                        rfl

theorem cell23_1875529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 5, 2].length) (baseStart_1875529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875529 prefixEnd_1875529 := by exact prefixLift 1875529
  have htrace : WordTrace (prefixWord ++ tailWord_1875529) baseStart_1875529 baseEnd_1875529 := by
    simpa [prefixWord, tailWord_1875529, baseEnd_1875529] using wordTrace_append hprefix tailTrace_1875529
  have hstable : (prefixWord ++ tailWord_1875529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875529).length < 2 ^ (prefixWord ++ tailWord_1875529).sum := by decide
  have hdescent : baseEnd_1875529 < baseStart_1875529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875543 : List Nat := [1, 1, 3, 2, 2, 5, 2, 2, 5]
def baseStart_1875543 : Nat := 118140960795 + 1875543 * 2 ^ 59
def prefixEnd_1875543 : Nat := 4983230072969 + 3 ^ 40 * 1875543 * 2
def baseEnd_1875543 : Nat := 107006116352851184787449

theorem tailTrace_1875543 : CollatzResearch.WordTrace tailWord_1875543 prefixEnd_1875543 107006116352851184787449 := by
  unfold tailWord_1875543
  simp only [CollatzResearch.WordTrace]
  refine ⟨68406673044235503087751283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45604448696157002058500855 68406673044235503087751283)
  ·
    refine ⟨102610009566353254631626925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68406673044235503087751283 102610009566353254631626925)
    ·
      refine ⟨38478753587382470486860097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102610009566353254631626925 38478753587382470486860097)
      ·
        refine ⟨28859065190536852865145073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38478753587382470486860097 28859065190536852865145073)
        ·
          refine ⟨21644298892902639648858805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28859065190536852865145073 21644298892902639648858805)
          ·
            refine ⟨2029153021209622467080513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21644298892902639648858805 2029153021209622467080513)
            ·
              refine ⟨1521864765907216850310385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029153021209622467080513 1521864765907216850310385)
              ·
                refine ⟨1141398574430412637732789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521864765907216850310385 1141398574430412637732789)
                ·
                  refine ⟨107006116352851184787449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1141398574430412637732789 107006116352851184787449)
                  ·
                    rfl

theorem cell23_1875543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 5].length) (baseStart_1875543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875543 prefixEnd_1875543 := by exact prefixLift 1875543
  have htrace : WordTrace (prefixWord ++ tailWord_1875543) baseStart_1875543 baseEnd_1875543 := by
    simpa [prefixWord, tailWord_1875543, baseEnd_1875543] using wordTrace_append hprefix tailTrace_1875543
  have hstable : (prefixWord ++ tailWord_1875543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875543).length < 2 ^ (prefixWord ++ tailWord_1875543).sum := by decide
  have hdescent : baseEnd_1875543 < baseStart_1875543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875552 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 8]
def baseStart_1875552 : Nat := 118140960795 + 1875552 * 2 ^ 59
def prefixEnd_1875552 : Nat := 4983230072969 + 3 ^ 40 * 1875552 * 2
def baseEnd_1875552 : Nat := 321019889500517042624833

theorem tailTrace_1875552 : CollatzResearch.WordTrace tailWord_1875552 prefixEnd_1875552 321019889500517042624833 := by
  unfold tailWord_1875552
  simp only [CollatzResearch.WordTrace]
  refine ⟨34203500650601448812414455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45604667534135265083219273 34203500650601448812414455)
  ·
    refine ⟨51305250975902173218621683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34203500650601448812414455 51305250975902173218621683)
    ·
      refine ⟨76957876463853259827932525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51305250975902173218621683 76957876463853259827932525)
      ·
        refine ⟨28859203673944972435474697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76957876463853259827932525 28859203673944972435474697)
        ·
          refine ⟨21644402755458729326606023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28859203673944972435474697 21644402755458729326606023)
          ·
            refine ⟨32466604133188093989909035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21644402755458729326606023 32466604133188093989909035)
            ·
              refine ⟨48699906199782140984863553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32466604133188093989909035 48699906199782140984863553)
              ·
                refine ⟨36524929649836605738647665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48699906199782140984863553 36524929649836605738647665)
                ·
                  refine ⟨27393697237377454303985749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36524929649836605738647665 27393697237377454303985749)
                  ·
                    refine ⟨321019889500517042624833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27393697237377454303985749 321019889500517042624833)
                    ·
                      rfl

theorem cell23_1875552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 8].length) (baseStart_1875552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875552 prefixEnd_1875552 := by exact prefixLift 1875552
  have htrace : WordTrace (prefixWord ++ tailWord_1875552) baseStart_1875552 baseEnd_1875552 := by
    simpa [prefixWord, tailWord_1875552, baseEnd_1875552] using wordTrace_append hprefix tailTrace_1875552
  have hstable : (prefixWord ++ tailWord_1875552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875552).length < 2 ^ (prefixWord ++ tailWord_1875552).sum := by decide
  have hdescent : baseEnd_1875552 < baseStart_1875552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875559 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1875559 : Nat := 118140960795 + 1875559 * 2 ^ 59
def prefixEnd_1875559 : Nat := 4983230072969 + 3 ^ 40 * 1875559 * 2
def baseEnd_1875559 : Nat := 963063262866132600486967

theorem tailTrace_1875559 : CollatzResearch.WordTrace tailWord_1875559 prefixEnd_1875559 963063262866132600486967 := by
  unfold tailWord_1875559
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407256612177537820333731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45604837741451691880222487 68407256612177537820333731)
  ·
    refine ⟨102610884918266306730500597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68407256612177537820333731 102610884918266306730500597)
    ·
      refine ⟨9619770461087466255984431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102610884918266306730500597 9619770461087466255984431)
      ·
        refine ⟨14429655691631199383976647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9619770461087466255984431 14429655691631199383976647)
        ·
          refine ⟨21644483537446799075964971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14429655691631199383976647 21644483537446799075964971)
          ·
            refine ⟨32466725306170198613947457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21644483537446799075964971 32466725306170198613947457)
            ·
              refine ⟨24350043979627648960460593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32466725306170198613947457 24350043979627648960460593)
              ·
                refine ⟨18262532984720736720345445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24350043979627648960460593 18262532984720736720345445)
                ·
                  refine ⟨3424224934635138135064771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18262532984720736720345445 3424224934635138135064771)
                  ·
                    refine ⟨5136337401952707202597157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3424224934635138135064771 5136337401952707202597157)
                    ·
                      refine ⟨963063262866132600486967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5136337401952707202597157 963063262866132600486967)
                      ·
                        rfl

theorem cell23_1875559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1875559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875559 prefixEnd_1875559 := by exact prefixLift 1875559
  have htrace : WordTrace (prefixWord ++ tailWord_1875559) baseStart_1875559 baseEnd_1875559 := by
    simpa [prefixWord, tailWord_1875559, baseEnd_1875559] using wordTrace_append hprefix tailTrace_1875559
  have hstable : (prefixWord ++ tailWord_1875559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875559).length < 2 ^ (prefixWord ++ tailWord_1875559).sum := by decide
  have hdescent : baseEnd_1875559 < baseStart_1875559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875573 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1875573 : Nat := 118140960795 + 1875573 * 2 ^ 59
def prefixEnd_1875573 : Nat := 4983230072969 + 3 ^ 40 * 1875573 * 2
def baseEnd_1875573 : Nat := 321023483865098515237301

theorem tailTrace_1875573 : CollatzResearch.WordTrace tailWord_1875573 prefixEnd_1875573 321023483865098515237301 := by
  unfold tailWord_1875573
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407767234126818211343373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45605178156084545474228915 68407767234126818211343373)
  ·
    refine ⟨25652912712797556829253765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68407767234126818211343373 25652912712797556829253765)
    ·
      refine ⟨4809921133649541905485081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25652912712797556829253765 4809921133649541905485081)
      ·
        refine ⟨3607440850237156429113811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4809921133649541905485081 3607440850237156429113811)
        ·
          refine ⟨5411161275355734643670717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607440850237156429113811 5411161275355734643670717)
          ·
            refine ⟨2029185478258400491376519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5411161275355734643670717 2029185478258400491376519)
            ·
              refine ⟨3043778217387600737064779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029185478258400491376519 3043778217387600737064779)
              ·
                refine ⟨4565667326081401105597169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043778217387600737064779 4565667326081401105597169)
                ·
                  refine ⟨3424250494561050829197877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565667326081401105597169 3424250494561050829197877)
                  ·
                    refine ⟨321023483865098515237301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3424250494561050829197877 321023483865098515237301)
                    ·
                      rfl

theorem cell23_1875573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1875573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875573 prefixEnd_1875573 := by exact prefixLift 1875573
  have htrace : WordTrace (prefixWord ++ tailWord_1875573) baseStart_1875573 baseEnd_1875573 := by
    simpa [prefixWord, tailWord_1875573, baseEnd_1875573] using wordTrace_append hprefix tailTrace_1875573
  have hstable : (prefixWord ++ tailWord_1875573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875573).length < 2 ^ (prefixWord ++ tailWord_1875573).sum := by decide
  have hdescent : baseEnd_1875573 < baseStart_1875573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875579 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3]
def baseStart_1875579 : Nat := 118140960795 + 1875579 * 2 ^ 59
def prefixEnd_1875579 : Nat := 4983230072969 + 3 ^ 40 * 1875579 * 2
def baseEnd_1875579 : Nat := 963073532479222522236875

theorem tailTrace_1875579 : CollatzResearch.WordTrace tailWord_1875579 prefixEnd_1875579 963073532479222522236875 := by
  unfold tailWord_1875579
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407986072105081236061791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45605324048070054157374527 68407986072105081236061791)
  ·
    refine ⟨102611979108157621854092687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68407986072105081236061791 102611979108157621854092687)
    ·
      refine ⟨153917968662236432781139031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102611979108157621854092687 153917968662236432781139031)
      ·
        refine ⟨230876952993354649171708547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153917968662236432781139031 230876952993354649171708547)
        ·
          refine ⟨346315429490031973757562821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230876952993354649171708547 346315429490031973757562821)
          ·
            refine ⟨64934143029380995079543029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 346315429490031973757562821 64934143029380995079543029)
            ·
              refine ⟨6087575909004468288707159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64934143029380995079543029 6087575909004468288707159)
              ·
                refine ⟨9131363863506702433060739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087575909004468288707159 9131363863506702433060739)
                ·
                  refine ⟨13697045795260053649591109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131363863506702433060739 13697045795260053649591109)
                  ·
                    refine ⟨2568196086611260059298333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13697045795260053649591109 2568196086611260059298333)
                    ·
                      refine ⟨963073532479222522236875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2568196086611260059298333 963073532479222522236875)
                      ·
                        rfl

theorem cell23_1875579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 4, 3].length) (baseStart_1875579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875579 prefixEnd_1875579 := by exact prefixLift 1875579
  have htrace : WordTrace (prefixWord ++ tailWord_1875579) baseStart_1875579 baseEnd_1875579 := by
    simpa [prefixWord, tailWord_1875579, baseEnd_1875579] using wordTrace_append hprefix tailTrace_1875579
  have hstable : (prefixWord ++ tailWord_1875579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875579).length < 2 ^ (prefixWord ++ tailWord_1875579).sum := by decide
  have hdescent : baseEnd_1875579 < baseStart_1875579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875637 : List Nat := [1, 3, 3, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1875637 : Nat := 118140960795 + 1875637 * 2 ^ 59
def prefixEnd_1875637 : Nat := 4983230072969 + 3 ^ 40 * 1875637 * 2
def baseEnd_1875637 : Nat := 321034438119061098437203

theorem tailTrace_1875637 : CollatzResearch.WordTrace tailWord_1875637 prefixEnd_1875637 321034438119061098437203 := by
  unfold tailWord_1875637
  simp only [CollatzResearch.WordTrace]
  refine ⟨68410101505894957141673165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45606734337263304761115443 68410101505894957141673165)
  ·
    refine ⟨25653788064710608928127437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68410101505894957141673165 25653788064710608928127437)
    ·
      refine ⟨9620170524266478348047789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25653788064710608928127437 9620170524266478348047789)
      ·
        refine ⟨3607563946599929380517921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9620170524266478348047789 3607563946599929380517921)
        ·
          refine ⟨2705672959949947035388441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3607563946599929380517921 2705672959949947035388441)
          ·
            refine ⟨2029254719962460276541331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2705672959949947035388441 2029254719962460276541331)
            ·
              refine ⟨3043882079943690414811997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029254719962460276541331 3043882079943690414811997)
              ·
                refine ⟨1141455779978883905554499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3043882079943690414811997 1141455779978883905554499)
                ·
                  refine ⟨1712183669968325858331749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141455779978883905554499 1712183669968325858331749)
                  ·
                    refine ⟨321034438119061098437203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712183669968325858331749 321034438119061098437203)
                    ·
                      rfl

theorem cell23_1875637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1875637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875637 prefixEnd_1875637 := by exact prefixLift 1875637
  have htrace : WordTrace (prefixWord ++ tailWord_1875637) baseStart_1875637 baseEnd_1875637 := by
    simpa [prefixWord, tailWord_1875637, baseEnd_1875637] using wordTrace_append hprefix tailTrace_1875637
  have hstable : (prefixWord ++ tailWord_1875637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875637).length < 2 ^ (prefixWord ++ tailWord_1875637).sum := by decide
  have hdescent : baseEnd_1875637 < baseStart_1875637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875679 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1875679 : Nat := 118140960795 + 1875679 * 2 ^ 59
def prefixEnd_1875679 : Nat := 4983230072969 + 3 ^ 40 * 1875679 * 2
def baseEnd_1875679 : Nat := 963124880544672130986415

theorem tailTrace_1875679 : CollatzResearch.WordTrace tailWord_1875679 prefixEnd_1875679 963124880544672130986415 := by
  unfold tailWord_1875679
  simp only [CollatzResearch.WordTrace]
  refine ⟨68411633371742798314702091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45607755581161865543134727 68411633371742798314702091)
  ·
    refine ⟨102617450057614197472053137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68411633371742798314702091 102617450057614197472053137)
    ·
      refine ⟨76963087543210648104039853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102617450057614197472053137 76963087543210648104039853)
      ·
        refine ⟨28861157828703993039014945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76963087543210648104039853 28861157828703993039014945)
        ·
          refine ⟨21645868371527994779261209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28861157828703993039014945 21645868371527994779261209)
          ·
            refine ⟨16234401278645996084445907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21645868371527994779261209 16234401278645996084445907)
            ·
              refine ⟨24351601917968994126668861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16234401278645996084445907 24351601917968994126668861)
              ·
                refine ⟨9131850719238372797500823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24351601917968994126668861 9131850719238372797500823)
                ·
                  refine ⟨13697776078857559196251235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9131850719238372797500823 13697776078857559196251235)
                  ·
                    refine ⟨20546664118286338794376853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13697776078857559196251235 20546664118286338794376853)
                    ·
                      refine ⟨963124880544672130986415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20546664118286338794376853 963124880544672130986415)
                      ·
                        rfl

theorem cell23_1875679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1875679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875679 prefixEnd_1875679 := by exact prefixLift 1875679
  have htrace : WordTrace (prefixWord ++ tailWord_1875679) baseStart_1875679 baseEnd_1875679 := by
    simpa [prefixWord, tailWord_1875679, baseEnd_1875679] using wordTrace_append hprefix tailTrace_1875679
  have hstable : (prefixWord ++ tailWord_1875679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875679).length < 2 ^ (prefixWord ++ tailWord_1875679).sum := by decide
  have hdescent : baseEnd_1875679 < baseStart_1875679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875683 : List Nat := [1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1875683 : Nat := 118140960795 + 1875683 * 2 ^ 59
def prefixEnd_1875683 : Nat := 4983230072969 + 3 ^ 40 * 1875683 * 2
def baseEnd_1875683 : Nat := 963126934467290115336397

theorem tailTrace_1875683 : CollatzResearch.WordTrace tailWord_1875683 prefixEnd_1875683 963126934467290115336397 := by
  unfold tailWord_1875683
  simp only [CollatzResearch.WordTrace]
  refine ⟨68411779263728306997847703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45607852842485537998565135 68411779263728306997847703)
  ·
    refine ⟨102617668895592460496771555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68411779263728306997847703 102617668895592460496771555)
    ·
      refine ⟨153926503343388690745157333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102617668895592460496771555 153926503343388690745157333)
      ·
        refine ⟨3607652422110672439339625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 153926503343388690745157333 3607652422110672439339625)
        ·
          refine ⟨2705739316583004329504719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3607652422110672439339625 2705739316583004329504719)
          ·
            refine ⟨4058608974874506494257079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705739316583004329504719 4058608974874506494257079)
            ·
              refine ⟨6087913462311759741385619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058608974874506494257079 6087913462311759741385619)
              ·
                refine ⟨9131870193467639612078429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6087913462311759741385619 9131870193467639612078429)
                ·
                  refine ⟨3424451322550364854529411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9131870193467639612078429 3424451322550364854529411)
                  ·
                    refine ⟨5136676983825547281794117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3424451322550364854529411 5136676983825547281794117)
                    ·
                      refine ⟨963126934467290115336397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5136676983825547281794117 963126934467290115336397)
                      ·
                        rfl

theorem cell23_1875683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1875683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875683 prefixEnd_1875683 := by exact prefixLift 1875683
  have htrace : WordTrace (prefixWord ++ tailWord_1875683) baseStart_1875683 baseEnd_1875683 := by
    simpa [prefixWord, tailWord_1875683, baseEnd_1875683] using wordTrace_append hprefix tailTrace_1875683
  have hstable : (prefixWord ++ tailWord_1875683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875683).length < 2 ^ (prefixWord ++ tailWord_1875683).sum := by decide
  have hdescent : baseEnd_1875683 < baseStart_1875683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875687 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1875687 : Nat := 118140960795 + 1875687 * 2 ^ 59
def prefixEnd_1875687 : Nat := 4983230072969 + 3 ^ 40 * 1875687 * 2
def baseEnd_1875687 : Nat := 963128988389908099686379

theorem tailTrace_1875687 : CollatzResearch.WordTrace tailWord_1875687 prefixEnd_1875687 963128988389908099686379 := by
  unfold tailWord_1875687
  simp only [CollatzResearch.WordTrace]
  refine ⟨68411925155713815680993315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45607950103809210453995543 68411925155713815680993315)
  ·
    refine ⟨102617887733570723521489973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68411925155713815680993315 102617887733570723521489973)
    ·
      refine ⟨9620426975022255330139685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102617887733570723521489973 9620426975022255330139685)
      ·
        refine ⟨1803830057816672874401191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9620426975022255330139685 1803830057816672874401191)
        ·
          refine ⟨2705745086725009311601787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803830057816672874401191 2705745086725009311601787)
          ·
            refine ⟨4058617630087513967402681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705745086725009311601787 4058617630087513967402681)
            ·
              refine ⟨3043963222565635475552011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058617630087513967402681 3043963222565635475552011)
              ·
                refine ⟨4565944833848453213328017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043963222565635475552011 4565944833848453213328017)
                ·
                  refine ⟨3424458625386339909996013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4565944833848453213328017 3424458625386339909996013)
                  ·
                    refine ⟨1284171984519877466248505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424458625386339909996013 1284171984519877466248505)
                    ·
                      refine ⟨963128988389908099686379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284171984519877466248505 963128988389908099686379)
                      ·
                        rfl

theorem cell23_1875687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1875687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875687 prefixEnd_1875687 := by exact prefixLift 1875687
  have htrace : WordTrace (prefixWord ++ tailWord_1875687) baseStart_1875687 baseEnd_1875687 := by
    simpa [prefixWord, tailWord_1875687, baseEnd_1875687] using wordTrace_append hprefix tailTrace_1875687
  have hstable : (prefixWord ++ tailWord_1875687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875687).length < 2 ^ (prefixWord ++ tailWord_1875687).sum := by decide
  have hdescent : baseEnd_1875687 < baseStart_1875687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875709 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 6]
def baseStart_1875709 : Nat := 118140960795 + 1875709 * 2 ^ 59
def prefixEnd_1875709 : Nat := 4983230072969 + 3 ^ 40 * 1875709 * 2
def baseEnd_1875709 : Nat := 963140284964307013611277

theorem tailTrace_1875709 : CollatzResearch.WordTrace tailWord_1875709 prefixEnd_1875709 963140284964307013611277 := by
  unfold tailWord_1875709
  simp only [CollatzResearch.WordTrace]
  refine ⟨68412727561634113438294181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45608485041089408958862787 68412727561634113438294181)
  ·
    refine ⟨12827386417806396269680159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68412727561634113438294181 12827386417806396269680159)
    ·
      refine ⟨19241079626709594404520239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12827386417806396269680159 19241079626709594404520239)
      ·
        refine ⟨28861619440064391606780359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19241079626709594404520239 28861619440064391606780359)
        ·
          refine ⟨43292429160096587410170539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28861619440064391606780359 43292429160096587410170539)
          ·
            refine ⟨64938643740144881115255809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43292429160096587410170539 64938643740144881115255809)
            ·
              refine ⟨48703982805108660836441857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64938643740144881115255809 48703982805108660836441857)
              ·
                refine ⟨36527987103831495627331393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48703982805108660836441857 36527987103831495627331393)
                ·
                  refine ⟨27395990327873621720498545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36527987103831495627331393 27395990327873621720498545)
                  ·
                    refine ⟨20546992745905216290373909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27395990327873621720498545 20546992745905216290373909)
                    ·
                      refine ⟨963140284964307013611277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20546992745905216290373909 963140284964307013611277)
                      ·
                        rfl

theorem cell23_1875709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_1875709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875709 prefixEnd_1875709 := by exact prefixLift 1875709
  have htrace : WordTrace (prefixWord ++ tailWord_1875709) baseStart_1875709 baseEnd_1875709 := by
    simpa [prefixWord, tailWord_1875709, baseEnd_1875709] using wordTrace_append hprefix tailTrace_1875709
  have hstable : (prefixWord ++ tailWord_1875709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875709).length < 2 ^ (prefixWord ++ tailWord_1875709).sum := by decide
  have hdescent : baseEnd_1875709 < baseStart_1875709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875729 : List Nat := [1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 5]
def baseStart_1875729 : Nat := 118140960795 + 1875729 * 2 ^ 59
def prefixEnd_1875729 : Nat := 4983230072969 + 3 ^ 40 * 1875729 * 2
def baseEnd_1875729 : Nat := 963150554577396935361185

theorem tailTrace_1875729 : CollatzResearch.WordTrace tailWord_1875729 prefixEnd_1875729 963150554577396935361185 := by
  unfold tailWord_1875729
  simp only [CollatzResearch.WordTrace]
  refine ⟨68413457021561656854022241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45608971347707771236014827 68413457021561656854022241)
  ·
    refine ⟨51310092766171242640516681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68413457021561656854022241 51310092766171242640516681)
    ·
      refine ⟨38482569574628431980387511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51310092766171242640516681 38482569574628431980387511)
      ·
        refine ⟨57723854361942647970581267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38482569574628431980387511 57723854361942647970581267)
        ·
          refine ⟨86585781542913971955871901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57723854361942647970581267 86585781542913971955871901)
          ·
            refine ⟨32469668078592739483451963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86585781542913971955871901 32469668078592739483451963)
            ·
              refine ⟨48704502117889109225177945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32469668078592739483451963 48704502117889109225177945)
              ·
                refine ⟨36528376588416831918883459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48704502117889109225177945 36528376588416831918883459)
                ·
                  refine ⟨54792564882625247878325189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36528376588416831918883459 54792564882625247878325189)
                  ·
                    refine ⟨10273605915492233977185973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54792564882625247878325189 10273605915492233977185973)
                    ·
                      refine ⟨963150554577396935361185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10273605915492233977185973 963150554577396935361185)
                      ·
                        rfl

theorem cell23_1875729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 5].length) (baseStart_1875729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875729 prefixEnd_1875729 := by exact prefixLift 1875729
  have htrace : WordTrace (prefixWord ++ tailWord_1875729) baseStart_1875729 baseEnd_1875729 := by
    simpa [prefixWord, tailWord_1875729, baseEnd_1875729] using wordTrace_append hprefix tailTrace_1875729
  have hstable : (prefixWord ++ tailWord_1875729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875729).length < 2 ^ (prefixWord ++ tailWord_1875729).sum := by decide
  have hdescent : baseEnd_1875729 < baseStart_1875729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875730 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1875730 : Nat := 118140960795 + 1875730 * 2 ^ 59
def prefixEnd_1875730 : Nat := 4983230072969 + 3 ^ 40 * 1875730 * 2
def baseEnd_1875730 : Nat := 963151068058051431448681

theorem tailTrace_1875730 : CollatzResearch.WordTrace tailWord_1875730 prefixEnd_1875730 963151068058051431448681 := by
  unfold tailWord_1875730
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103373373639508506202161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45608995663038689349872429 17103373373639508506202161)
  ·
    refine ⟨12827530030229631379651621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17103373373639508506202161 12827530030229631379651621)
    ·
      refine ⟨2405161880668055883684679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12827530030229631379651621 2405161880668055883684679)
      ·
        refine ⟨3607742821002083825527019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405161880668055883684679 3607742821002083825527019)
        ·
          refine ⟨5411614231503125738290529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607742821002083825527019 5411614231503125738290529)
          ·
            refine ⟨4058710673627344303717897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5411614231503125738290529 4058710673627344303717897)
            ·
              refine ⟨3044033005220508227788423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058710673627344303717897 3044033005220508227788423)
              ·
                refine ⟨4566049507830762341682635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044033005220508227788423 4566049507830762341682635)
                ·
                  refine ⟨6849074261746143512523953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566049507830762341682635 6849074261746143512523953)
                  ·
                    refine ⟨5136805696309607634392965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849074261746143512523953 5136805696309607634392965)
                    ·
                      refine ⟨963151068058051431448681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5136805696309607634392965 963151068058051431448681)
                      ·
                        rfl

theorem cell23_1875730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1875730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875730 prefixEnd_1875730 := by exact prefixLift 1875730
  have htrace : WordTrace (prefixWord ++ tailWord_1875730) baseStart_1875730 baseEnd_1875730 := by
    simpa [prefixWord, tailWord_1875730, baseEnd_1875730] using wordTrace_append hprefix tailTrace_1875730
  have hstable : (prefixWord ++ tailWord_1875730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875730).length < 2 ^ (prefixWord ++ tailWord_1875730).sum := by decide
  have hdescent : baseEnd_1875730 < baseStart_1875730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875733 : List Nat := [1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_1875733 : Nat := 118140960795 + 1875733 * 2 ^ 59
def prefixEnd_1875733 : Nat := 4983230072969 + 3 ^ 40 * 1875733 * 2
def baseEnd_1875733 : Nat := 963152608500014919711167

theorem tailTrace_1875733 : CollatzResearch.WordTrace tailWord_1875733 prefixEnd_1875733 963152608500014919711167 := by
  unfold tailWord_1875733
  simp only [CollatzResearch.WordTrace]
  refine ⟨68413602913547165537167853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45609068609031443691445235 68413602913547165537167853)
  ·
    refine ⟨25655101092580187076437945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68413602913547165537167853 25655101092580187076437945)
    ·
      refine ⟨19241325819435140307328459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25655101092580187076437945 19241325819435140307328459)
      ·
        refine ⟨28861988729152710460992689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19241325819435140307328459 28861988729152710460992689)
        ·
          refine ⟨21646491546864532845744517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28861988729152710460992689 21646491546864532845744517)
          ·
            refine ⟨4058717165037099908577097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21646491546864532845744517 4058717165037099908577097)
            ·
              refine ⟨3044037873777824931432823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058717165037099908577097 3044037873777824931432823)
              ·
                refine ⟨4566056810666737397149235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044037873777824931432823 4566056810666737397149235)
                ·
                  refine ⟨6849085216000106095723853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566056810666737397149235 6849085216000106095723853)
                  ·
                    refine ⟨2568406956000039785896445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6849085216000106095723853 2568406956000039785896445)
                    ·
                      refine ⟨963152608500014919711167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2568406956000039785896445 963152608500014919711167)
                      ·
                        rfl

theorem cell23_1875733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_1875733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875733 prefixEnd_1875733 := by exact prefixLift 1875733
  have htrace : WordTrace (prefixWord ++ tailWord_1875733) baseStart_1875733 baseEnd_1875733 := by
    simpa [prefixWord, tailWord_1875733, baseEnd_1875733] using wordTrace_append hprefix tailTrace_1875733
  have hstable : (prefixWord ++ tailWord_1875733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875733).length < 2 ^ (prefixWord ++ tailWord_1875733).sum := by decide
  have hdescent : baseEnd_1875733 < baseStart_1875733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875743 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 3, 3, 2]
def baseStart_1875743 : Nat := 118140960795 + 1875743 * 2 ^ 59
def prefixEnd_1875743 : Nat := 4983230072969 + 3 ^ 40 * 1875743 * 2
def baseEnd_1875743 : Nat := 963157743306559880586121

theorem tailTrace_1875743 : CollatzResearch.WordTrace tailWord_1875743 prefixEnd_1875743 963157743306559880586121 := by
  unfold tailWord_1875743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68413967643510937245031883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45609311762340624830021255 68413967643510937245031883)
  ·
    refine ⟨102620951465266405867547825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68413967643510937245031883 102620951465266405867547825)
    ·
      refine ⟨76965713598949804400660869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102620951465266405867547825 76965713598949804400660869)
      ·
        refine ⟨14431071299803088325123913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76965713598949804400660869 14431071299803088325123913)
        ·
          refine ⟨10823303474852316243842935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14431071299803088325123913 10823303474852316243842935)
          ·
            refine ⟨16234955212278474365764403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823303474852316243842935 16234955212278474365764403)
            ·
              refine ⟨24352432818417711548646605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16234955212278474365764403 24352432818417711548646605)
              ·
                refine ⟨9132162306906641830742477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24352432818417711548646605 9132162306906641830742477)
                ·
                  refine ⟨3424560865089990686528429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9132162306906641830742477 3424560865089990686528429)
                  ·
                    refine ⟨1284210324408746507448161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424560865089990686528429 1284210324408746507448161)
                    ·
                      refine ⟨963157743306559880586121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284210324408746507448161 963157743306559880586121)
                      ·
                        rfl

theorem cell23_1875743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_1875743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875743 prefixEnd_1875743 := by exact prefixLift 1875743
  have htrace : WordTrace (prefixWord ++ tailWord_1875743) baseStart_1875743 baseEnd_1875743 := by
    simpa [prefixWord, tailWord_1875743, baseEnd_1875743] using wordTrace_append hprefix tailTrace_1875743
  have hstable : (prefixWord ++ tailWord_1875743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875743).length < 2 ^ (prefixWord ++ tailWord_1875743).sum := by decide
  have hdescent : baseEnd_1875743 < baseStart_1875743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875746 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1875746 : Nat := 118140960795 + 1875746 * 2 ^ 59
def prefixEnd_1875746 : Nat := 4983230072969 + 3 ^ 40 * 1875746 * 2
def baseEnd_1875746 : Nat := 963159283748523368848607

theorem tailTrace_1875746 : CollatzResearch.WordTrace tailWord_1875746 prefixEnd_1875746 963159283748523368848607 := by
  unfold tailWord_1875746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103519265625017189347773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45609384708333379171594061 17103519265625017189347773)
  ·
    refine ⟨6413819724609381446005415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17103519265625017189347773 6413819724609381446005415)
    ·
      refine ⟨9620729586914072169008123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413819724609381446005415 9620729586914072169008123)
      ·
        refine ⟨14431094380371108253512185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9620729586914072169008123 14431094380371108253512185)
        ·
          refine ⟨10823320785278331190134139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14431094380371108253512185 10823320785278331190134139)
          ·
            refine ⟨16234981177917496785201209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823320785278331190134139 16234981177917496785201209)
            ·
              refine ⟨12176235883438122588900907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16234981177917496785201209 12176235883438122588900907)
              ·
                refine ⟨18264353825157183883351361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12176235883438122588900907 18264353825157183883351361)
                ·
                  refine ⟨13698265368867887912513521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18264353825157183883351361 13698265368867887912513521)
                  ·
                    refine ⟨10273699026650915934385141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13698265368867887912513521 10273699026650915934385141)
                    ·
                      refine ⟨963159283748523368848607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10273699026650915934385141 963159283748523368848607)
                      ·
                        rfl

theorem cell23_1875746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1875746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875746 prefixEnd_1875746 := by exact prefixLift 1875746
  have htrace : WordTrace (prefixWord ++ tailWord_1875746) baseStart_1875746 baseEnd_1875746 := by
    simpa [prefixWord, tailWord_1875746, baseEnd_1875746] using wordTrace_append hprefix tailTrace_1875746
  have hstable : (prefixWord ++ tailWord_1875746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875746).length < 2 ^ (prefixWord ++ tailWord_1875746).sum := by decide
  have hdescent : baseEnd_1875746 < baseStart_1875746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875786 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4]
def baseStart_1875786 : Nat := 118140960795 + 1875786 * 2 ^ 59
def prefixEnd_1875786 : Nat := 4983230072969 + 3 ^ 40 * 1875786 * 2
def baseEnd_1875786 : Nat := 963179822974703212348423

theorem tailTrace_1875786 : CollatzResearch.WordTrace tailWord_1875786 prefixEnd_1875786 963179822974703212348423 := by
  unfold tailWord_1875786
  simp only [CollatzResearch.WordTrace]
  refine ⟨17103883995588788897211803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45610357321570103725898141 17103883995588788897211803)
  ·
    refine ⟨25655825993383183345817705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17103883995588788897211803 25655825993383183345817705)
    ·
      refine ⟨19241869495037387509363279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25655825993383183345817705 19241869495037387509363279)
      ·
        refine ⟨28862804242556081264044919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19241869495037387509363279 28862804242556081264044919)
        ·
          refine ⟨43294206363834121896067379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28862804242556081264044919 43294206363834121896067379)
          ·
            refine ⟨64941309545751182844101069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43294206363834121896067379 64941309545751182844101069)
            ·
              refine ⟨24352991079656693566537901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64941309545751182844101069 24352991079656693566537901)
              ·
                refine ⟨9132371654871260087451713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24352991079656693566537901 9132371654871260087451713)
                ·
                  refine ⟨6849278741153445065588785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9132371654871260087451713 6849278741153445065588785)
                  ·
                    refine ⟨5136959055865083799191589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6849278741153445065588785 5136959055865083799191589)
                    ·
                      refine ⟨963179822974703212348423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5136959055865083799191589 963179822974703212348423)
                      ·
                        rfl

theorem cell23_1875786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_1875786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875786 prefixEnd_1875786 := by exact prefixLift 1875786
  have htrace : WordTrace (prefixWord ++ tailWord_1875786) baseStart_1875786 baseEnd_1875786 := by
    simpa [prefixWord, tailWord_1875786, baseEnd_1875786] using wordTrace_append hprefix tailTrace_1875786
  have hstable : (prefixWord ++ tailWord_1875786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875786).length < 2 ^ (prefixWord ++ tailWord_1875786).sum := by decide
  have hdescent : baseEnd_1875786 < baseStart_1875786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875833 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 5, 2]
def baseStart_1875833 : Nat := 118140960795 + 1875833 * 2 ^ 59
def prefixEnd_1875833 : Nat := 4983230072969 + 3 ^ 40 * 1875833 * 2
def baseEnd_1875833 : Nat := 963203956565464528460707

theorem tailTrace_1875833 : CollatzResearch.WordTrace tailWord_1875833 prefixEnd_1875833 963203956565464528460707 := by
  unfold tailWord_1875833
  simp only [CollatzResearch.WordTrace]
  refine ⟨68417250213184882615808153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45611500142123255077205435 68417250213184882615808153)
  ·
    refine ⟨51312937659888661961856115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68417250213184882615808153 51312937659888661961856115)
    ·
      refine ⟨76969406489832992942784173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51312937659888661961856115 76969406489832992942784173)
      ·
        refine ⟨28863527433687372353544065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76969406489832992942784173 28863527433687372353544065)
        ·
          refine ⟨21647645575265529265158049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28863527433687372353544065 21647645575265529265158049)
          ·
            refine ⟨16235734181449146948868537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21647645575265529265158049 16235734181449146948868537)
            ·
              refine ⟨12176800636086860211651403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16235734181449146948868537 12176800636086860211651403)
              ·
                refine ⟨18265200954130290317477105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12176800636086860211651403 18265200954130290317477105)
                ·
                  refine ⟨13698900715597717738107829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18265200954130290317477105 13698900715597717738107829)
                  ·
                    refine ⟨1284271942087286037947609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13698900715597717738107829 1284271942087286037947609)
                    ·
                      refine ⟨963203956565464528460707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284271942087286037947609 963203956565464528460707)
                      ·
                        rfl

theorem cell23_1875833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 5, 2].length) (baseStart_1875833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875833 prefixEnd_1875833 := by exact prefixLift 1875833
  have htrace : WordTrace (prefixWord ++ tailWord_1875833) baseStart_1875833 baseEnd_1875833 := by
    simpa [prefixWord, tailWord_1875833, baseEnd_1875833] using wordTrace_append hprefix tailTrace_1875833
  have hstable : (prefixWord ++ tailWord_1875833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875833).length < 2 ^ (prefixWord ++ tailWord_1875833).sum := by decide
  have hdescent : baseEnd_1875833 < baseStart_1875833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875860 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 2, 5]
def baseStart_1875860 : Nat := 118140960795 + 1875860 * 2 ^ 59
def prefixEnd_1875860 : Nat := 4983230072969 + 3 ^ 40 * 1875860 * 2
def baseEnd_1875860 : Nat := 321072606847711974274361

theorem tailTrace_1875860 : CollatzResearch.WordTrace tailWord_1875860 prefixEnd_1875860 321072606847711974274361 := by
  unfold tailWord_1875860
  simp only [CollatzResearch.WordTrace]
  refine ⟨34209117492043533113520517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45612156656058044151360689 34209117492043533113520517)
  ·
    refine ⟨6414209529758162458785097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34209117492043533113520517 6414209529758162458785097)
    ·
      refine ⟨4810657147318621844088823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6414209529758162458785097 4810657147318621844088823)
      ·
        refine ⟨7215985720977932766133235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810657147318621844088823 7215985720977932766133235)
        ·
          refine ⟨10823978581466899149199853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215985720977932766133235 10823978581466899149199853)
          ·
            refine ⟨4058991968050087180949945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10823978581466899149199853 4058991968050087180949945)
            ·
              refine ⟨3044243976037565385712459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058991968050087180949945 3044243976037565385712459)
              ·
                refine ⟨4566365964056348078568689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044243976037565385712459 4566365964056348078568689)
                ·
                  refine ⟨3424774473042261058926517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4566365964056348078568689 3424774473042261058926517)
                  ·
                    refine ⟨321072606847711974274361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3424774473042261058926517 321072606847711974274361)
                    ·
                      rfl

theorem cell23_1875860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_1875860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875860 prefixEnd_1875860 := by exact prefixLift 1875860
  have htrace : WordTrace (prefixWord ++ tailWord_1875860) baseStart_1875860 baseEnd_1875860 := by
    simpa [prefixWord, tailWord_1875860, baseEnd_1875860] using wordTrace_append hprefix tailTrace_1875860
  have hstable : (prefixWord ++ tailWord_1875860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875860).length < 2 ^ (prefixWord ++ tailWord_1875860).sum := by decide
  have hdescent : baseEnd_1875860 < baseStart_1875860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875863 : List Nat := [1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1875863 : Nat := 118140960795 + 1875863 * 2 ^ 59
def prefixEnd_1875863 : Nat := 4983230072969 + 3 ^ 40 * 1875863 * 2
def baseEnd_1875863 : Nat := 963219360985099411085569

theorem tailTrace_1875863 : CollatzResearch.WordTrace tailWord_1875863 prefixEnd_1875863 963219360985099411085569 := by
  unfold tailWord_1875863
  simp only [CollatzResearch.WordTrace]
  refine ⟨68418344403076197739400243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45612229602050798492933495 68418344403076197739400243)
  ·
    refine ⟨102627516604614296609100365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68418344403076197739400243 102627516604614296609100365)
    ·
      refine ⟨38485318726730361228412637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102627516604614296609100365 38485318726730361228412637)
      ·
        refine ⟨14431994522523885460654739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38485318726730361228412637 14431994522523885460654739)
        ·
          refine ⟨21647991783785828190982109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14431994522523885460654739 21647991783785828190982109)
          ·
            refine ⟨8117996918919685571618291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21647991783785828190982109 8117996918919685571618291)
            ·
              refine ⟨12176995378379528357427437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117996918919685571618291 12176995378379528357427437)
              ·
                refine ⟨4566373266892323134035289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12176995378379528357427437 4566373266892323134035289)
                ·
                  refine ⟨3424779950169242350526467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4566373266892323134035289 3424779950169242350526467)
                  ·
                    refine ⟨5137169925253863525789701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3424779950169242350526467 5137169925253863525789701)
                    ·
                      refine ⟨963219360985099411085569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5137169925253863525789701 963219360985099411085569)
                      ·
                        rfl

theorem cell23_1875863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1875863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875863 prefixEnd_1875863 := by exact prefixLift 1875863
  have htrace : WordTrace (prefixWord ++ tailWord_1875863) baseStart_1875863 baseEnd_1875863 := by
    simpa [prefixWord, tailWord_1875863, baseEnd_1875863] using wordTrace_append hprefix tailTrace_1875863
  have hstable : (prefixWord ++ tailWord_1875863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875863).length < 2 ^ (prefixWord ++ tailWord_1875863).sum := by decide
  have hdescent : baseEnd_1875863 < baseStart_1875863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875940 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 4, 3, 2]
def baseStart_1875940 : Nat := 118140960795 + 1875940 * 2 ^ 59
def prefixEnd_1875940 : Nat := 4983230072969 + 3 ^ 40 * 1875940 * 2
def baseEnd_1875940 : Nat := 963258898995495609822715

theorem tailTrace_1875940 : CollatzResearch.WordTrace tailWord_1875940 prefixEnd_1875940 963258898995495609822715 := by
  unfold tailWord_1875940
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210576411898619944976637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45614101882531493259968849 34210576411898619944976637)
  ·
    refine ⟨12828966154461982479366239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34210576411898619944976637 12828966154461982479366239)
    ·
      refine ⟨19243449231692973719049359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12828966154461982479366239 19243449231692973719049359)
      ·
        refine ⟨28865173847539460578574039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19243449231692973719049359 28865173847539460578574039)
        ·
          refine ⟨43297760771309190867861059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28865173847539460578574039 43297760771309190867861059)
          ·
            refine ⟨64946641156963786301791589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43297760771309190867861059 64946641156963786301791589)
            ·
              refine ⟨12177495216930709931585923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64946641156963786301791589 12177495216930709931585923)
              ·
                refine ⟨18266242825396064897378885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12177495216930709931585923 18266242825396064897378885)
                ·
                  refine ⟨3424920529761762168258541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18266242825396064897378885 3424920529761762168258541)
                  ·
                    refine ⟨1284345198660660813096953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3424920529761762168258541 1284345198660660813096953)
                    ·
                      refine ⟨963258898995495609822715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284345198660660813096953 963258898995495609822715)
                      ·
                        rfl

theorem cell23_1875940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 3, 2].length) (baseStart_1875940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875940 prefixEnd_1875940 := by exact prefixLift 1875940
  have htrace : WordTrace (prefixWord ++ tailWord_1875940) baseStart_1875940 baseEnd_1875940 := by
    simpa [prefixWord, tailWord_1875940, baseEnd_1875940] using wordTrace_append hprefix tailTrace_1875940
  have hstable : (prefixWord ++ tailWord_1875940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875940).length < 2 ^ (prefixWord ++ tailWord_1875940).sum := by decide
  have hdescent : baseEnd_1875940 < baseStart_1875940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875963 : List Nat := [1, 1, 1, 1, 1, 3, 7, 1, 1, 6]
def baseStart_1875963 : Nat := 118140960795 + 1875963 * 2 ^ 59
def prefixEnd_1875963 : Nat := 4983230072969 + 3 ^ 40 * 1875963 * 2
def baseEnd_1875963 : Nat := 321090236350183006611703

theorem tailTrace_1875963 : CollatzResearch.WordTrace tailWord_1875963 prefixEnd_1875963 321090236350183006611703 := by
  unfold tailWord_1875963
  simp only [CollatzResearch.WordTrace]
  refine ⟨68421991702713914818040543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45614661135142609878693695 68421991702713914818040543)
  ·
    refine ⟨102632987554070872227060815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68421991702713914818040543 102632987554070872227060815)
    ·
      refine ⟨153949481331106308340591223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102632987554070872227060815 153949481331106308340591223)
      ·
        refine ⟨230924221996659462510886835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153949481331106308340591223 230924221996659462510886835)
        ·
          refine ⟨346386332994989193766330253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230924221996659462510886835 346386332994989193766330253)
          ·
            refine ⟨129894874873120947662373845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346386332994989193766330253 129894874873120947662373845)
            ·
              refine ⟨3044411129838772210836887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129894874873120947662373845 3044411129838772210836887)
              ·
                refine ⟨4566616694758158316255331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044411129838772210836887 4566616694758158316255331)
                ·
                  refine ⟨6849925042137237474382997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4566616694758158316255331 6849925042137237474382997)
                  ·
                    refine ⟨321090236350183006611703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6849925042137237474382997 321090236350183006611703)
                    ·
                      rfl

theorem cell23_1875963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 6].length) (baseStart_1875963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1875963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1875963 prefixEnd_1875963 := by exact prefixLift 1875963
  have htrace : WordTrace (prefixWord ++ tailWord_1875963) baseStart_1875963 baseEnd_1875963 := by
    simpa [prefixWord, tailWord_1875963, baseEnd_1875963] using wordTrace_append hprefix tailTrace_1875963
  have hstable : (prefixWord ++ tailWord_1875963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875963).length < 2 ^ (prefixWord ++ tailWord_1875963).sum := by decide
  have hdescent : baseEnd_1875963 < baseStart_1875963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876010 : List Nat := [3, 1, 4, 1, 2, 2, 2, 8]
def baseStart_1876010 : Nat := 118140960795 + 1876010 * 2 ^ 59
def prefixEnd_1876010 : Nat := 4983230072969 + 3 ^ 40 * 1876010 * 2
def baseEnd_1876010 : Nat := 35677586764492975405459

theorem tailTrace_1876010 : CollatzResearch.WordTrace tailWord_1876010 prefixEnd_1876010 35677586764492975405459 := by
  unfold tailWord_1876010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105926483385910461250371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45615803955695761230000989 17105926483385910461250371)
  ·
    refine ⟨25658889725078865691875557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17105926483385910461250371 25658889725078865691875557)
    ·
      refine ⟨4811041823452287317226667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25658889725078865691875557 4811041823452287317226667)
      ·
        refine ⟨7216562735178430975840001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811041823452287317226667 7216562735178430975840001)
        ·
          refine ⟨5412422051383823231880001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216562735178430975840001 5412422051383823231880001)
          ·
            refine ⟨4059316538537867423910001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5412422051383823231880001 4059316538537867423910001)
            ·
              refine ⟨3044487403903400567932501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4059316538537867423910001 3044487403903400567932501)
              ·
                refine ⟨35677586764492975405459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3044487403903400567932501 35677586764492975405459)
                ·
                  rfl

theorem cell23_1876010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 2, 8].length) (baseStart_1876010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876010 prefixEnd_1876010 := by exact prefixLift 1876010
  have htrace : WordTrace (prefixWord ++ tailWord_1876010) baseStart_1876010 baseEnd_1876010 := by
    simpa [prefixWord, tailWord_1876010, baseEnd_1876010] using wordTrace_append hprefix tailTrace_1876010
  have hstable : (prefixWord ++ tailWord_1876010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876010).length < 2 ^ (prefixWord ++ tailWord_1876010).sum := by decide
  have hdescent : baseEnd_1876010 < baseStart_1876010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876014 : List Nat := [4, 1, 3, 1, 1, 2, 4, 1, 2, 4]
def baseStart_1876014 : Nat := 118140960795 + 1876014 * 2 ^ 59
def prefixEnd_1876014 : Nat := 4983230072969 + 3 ^ 40 * 1876014 * 2
def baseEnd_1876014 : Nat := 321098965521309440099125

theorem tailTrace_1876014 : CollatzResearch.WordTrace tailWord_1876014 prefixEnd_1876014 321098965521309440099125 := by
  unfold tailWord_1876014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8552981478191143816018387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45615901217019433685431397 8552981478191143816018387)
  ·
    refine ⟨12829472217286715724027581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8552981478191143816018387 12829472217286715724027581)
    ·
      refine ⟨4811052081482518396510343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12829472217286715724027581 4811052081482518396510343)
      ·
        refine ⟨7216578122223777594765515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811052081482518396510343 7216578122223777594765515)
        ·
          refine ⟨10824867183335666392148273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216578122223777594765515 10824867183335666392148273)
          ·
            refine ⟨8118650387501749794111205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10824867183335666392148273 8118650387501749794111205)
            ·
              refine ⟨1522246947656578086395851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8118650387501749794111205 1522246947656578086395851)
              ·
                refine ⟨2283370421484867129593777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522246947656578086395851 2283370421484867129593777)
                ·
                  refine ⟨1712527816113650347195333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2283370421484867129593777 1712527816113650347195333)
                  ·
                    refine ⟨321098965521309440099125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712527816113650347195333 321098965521309440099125)
                    ·
                      rfl

theorem cell23_1876014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_1876014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876014 prefixEnd_1876014 := by exact prefixLift 1876014
  have htrace : WordTrace (prefixWord ++ tailWord_1876014) baseStart_1876014 baseEnd_1876014 := by
    simpa [prefixWord, tailWord_1876014, baseEnd_1876014] using wordTrace_append hprefix tailTrace_1876014
  have hstable : (prefixWord ++ tailWord_1876014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876014).length < 2 ^ (prefixWord ++ tailWord_1876014).sum := by decide
  have hdescent : baseEnd_1876014 < baseStart_1876014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876024 : List Nat := [2, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_1876024 : Nat := 118140960795 + 1876024 * 2 ^ 59
def prefixEnd_1876024 : Nat := 4983230072969 + 3 ^ 40 * 1876024 * 2
def baseEnd_1876024 : Nat := 963302031370473281172329

theorem tailTrace_1876024 : CollatzResearch.WordTrace tailWord_1876024 prefixEnd_1876024 963302031370473281172329 := by
  unfold tailWord_1876024
  simp only [CollatzResearch.WordTrace]
  refine ⟨34212108277746461118005563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45616144370328614824007417 34212108277746461118005563)
  ·
    refine ⟨51318162416619691677008345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34212108277746461118005563 51318162416619691677008345)
    ·
      refine ⟨38488621812464768757756259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51318162416619691677008345 38488621812464768757756259)
      ·
        refine ⟨57732932718697153136634389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38488621812464768757756259 57732932718697153136634389)
        ·
          refine ⟨2706231221188929053279737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57732932718697153136634389 2706231221188929053279737)
          ·
            refine ⟨2029673415891696789959803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706231221188929053279737 2029673415891696789959803)
            ·
              refine ⟨3044510123837545184939705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029673415891696789959803 3044510123837545184939705)
              ·
                refine ⟨2283382592878158888704779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3044510123837545184939705 2283382592878158888704779)
                ·
                  refine ⟨3425073889317238333057169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2283382592878158888704779 3425073889317238333057169)
                  ·
                    refine ⟨2568805416987928749792877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425073889317238333057169 2568805416987928749792877)
                    ·
                      refine ⟨963302031370473281172329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2568805416987928749792877 963302031370473281172329)
                      ·
                        rfl

theorem cell23_1876024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_1876024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876024 prefixEnd_1876024 := by exact prefixLift 1876024
  have htrace : WordTrace (prefixWord ++ tailWord_1876024) baseStart_1876024 baseEnd_1876024 := by
    simpa [prefixWord, tailWord_1876024, baseEnd_1876024] using wordTrace_append hprefix tailTrace_1876024
  have hstable : (prefixWord ++ tailWord_1876024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876024).length < 2 ^ (prefixWord ++ tailWord_1876024).sum := by decide
  have hdescent : baseEnd_1876024 < baseStart_1876024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876038 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1876038 : Nat := 118140960795 + 1876038 * 2 ^ 59
def prefixEnd_1876038 : Nat := 4983230072969 + 3 ^ 40 * 1876038 * 2
def baseEnd_1876038 : Nat := 963309220099636226397265

theorem tailTrace_1876038 : CollatzResearch.WordTrace tailWord_1876038 prefixEnd_1876038 963309220099636226397265 := by
  unfold tailWord_1876038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138272724295068832094399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45616484784961468418013845 2138272724295068832094399)
  ·
    refine ⟨3207409086442603248141599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138272724295068832094399 3207409086442603248141599)
    ·
      refine ⟨4811113629663904872212399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3207409086442603248141599 4811113629663904872212399)
      ·
        refine ⟨7216670444495857308318599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811113629663904872212399 7216670444495857308318599)
        ·
          refine ⟨10825005666743785962477899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216670444495857308318599 10825005666743785962477899)
          ·
            refine ⟨16237508500115678943716849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825005666743785962477899 16237508500115678943716849)
            ·
              refine ⟨12178131375086759207787637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16237508500115678943716849 12178131375086759207787637)
              ·
                refine ⟨1141699816414383675730091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12178131375086759207787637 1141699816414383675730091)
                ·
                  refine ⟨1712549724621575513595137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141699816414383675730091 1712549724621575513595137)
                  ·
                    refine ⟨1284412293466181635196353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1712549724621575513595137 1284412293466181635196353)
                    ·
                      refine ⟨963309220099636226397265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284412293466181635196353 963309220099636226397265)
                      ·
                        rfl

theorem cell23_1876038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1876038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876038 prefixEnd_1876038 := by exact prefixLift 1876038
  have htrace : WordTrace (prefixWord ++ tailWord_1876038) baseStart_1876038 baseEnd_1876038 := by
    simpa [prefixWord, tailWord_1876038, baseEnd_1876038] using wordTrace_append hprefix tailTrace_1876038
  have hstable : (prefixWord ++ tailWord_1876038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876038).length < 2 ^ (prefixWord ++ tailWord_1876038).sum := by decide
  have hdescent : baseEnd_1876038 < baseStart_1876038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876060 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1876060 : Nat := 118140960795 + 1876060 * 2 ^ 59
def prefixEnd_1876060 : Nat := 4983230072969 + 3 ^ 40 * 1876060 * 2
def baseEnd_1876060 : Nat := 963320516674035140322163

theorem tailTrace_1876060 : CollatzResearch.WordTrace tailWord_1876060 prefixEnd_1876060 963320516674035140322163 := by
  unfold tailWord_1876060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34212764791681250192160817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45617019722241666922881089 34212764791681250192160817)
  ·
    refine ⟨25659573593760937644120613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34212764791681250192160817 25659573593760937644120613)
    ·
      refine ⟨4811170048830175808272615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25659573593760937644120613 4811170048830175808272615)
      ·
        refine ⟨7216755073245263712408923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811170048830175808272615 7216755073245263712408923)
        ·
          refine ⟨10825132609867895568613385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7216755073245263712408923 10825132609867895568613385)
          ·
            refine ⟨8118849457400921676460039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10825132609867895568613385 8118849457400921676460039)
            ·
              refine ⟨12178274186101382514690059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118849457400921676460039 12178274186101382514690059)
              ·
                refine ⟨18267411279152073772035089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12178274186101382514690059 18267411279152073772035089)
                ·
                  refine ⟨13700558459364055329026317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18267411279152073772035089 13700558459364055329026317)
                  ·
                    refine ⟨5137709422261520748384869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13700558459364055329026317 5137709422261520748384869)
                    ·
                      refine ⟨963320516674035140322163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5137709422261520748384869 963320516674035140322163)
                      ·
                        rfl

theorem cell23_1876060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1876060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876060 prefixEnd_1876060 := by exact prefixLift 1876060
  have htrace : WordTrace (prefixWord ++ tailWord_1876060) baseStart_1876060 baseEnd_1876060 := by
    simpa [prefixWord, tailWord_1876060, baseEnd_1876060] using wordTrace_append hprefix tailTrace_1876060
  have hstable : (prefixWord ++ tailWord_1876060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876060).length < 2 ^ (prefixWord ++ tailWord_1876060).sum := by decide
  have hdescent : baseEnd_1876060 < baseStart_1876060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876063 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1876063 : Nat := 118140960795 + 1876063 * 2 ^ 59
def prefixEnd_1876063 : Nat := 4983230072969 + 3 ^ 40 * 1876063 * 2
def baseEnd_1876063 : Nat := 963322057115998628584649

theorem tailTrace_1876063 : CollatzResearch.WordTrace tailWord_1876063 prefixEnd_1876063 963322057115998628584649 := by
  unfold tailWord_1876063
  simp only [CollatzResearch.WordTrace]
  refine ⟨68425639002351631896680843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45617092668234421264453895 68425639002351631896680843)
  ·
    refine ⟨102638458503527447845021265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68425639002351631896680843 102638458503527447845021265)
    ·
      refine ⟨76978843877645585883765949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102638458503527447845021265 76978843877645585883765949)
      ·
        refine ⟨28867066454117094706412231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76978843877645585883765949 28867066454117094706412231)
        ·
          refine ⟨43300599681175642059618347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28867066454117094706412231 43300599681175642059618347)
          ·
            refine ⟨64950899521763463089427521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43300599681175642059618347 64950899521763463089427521)
            ·
              refine ⟨48713174641322597317070641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64950899521763463089427521 48713174641322597317070641)
              ·
                refine ⟨36534880980991947987802981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48713174641322597317070641 36534880980991947987802981)
                ·
                  refine ⟨6850290183935990247713059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36534880980991947987802981 6850290183935990247713059)
                  ·
                    refine ⟨10275435275903985371569589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6850290183935990247713059 10275435275903985371569589)
                    ·
                      refine ⟨963322057115998628584649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10275435275903985371569589 963322057115998628584649)
                      ·
                        rfl

theorem cell23_1876063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1876063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876063 prefixEnd_1876063 := by exact prefixLift 1876063
  have htrace : WordTrace (prefixWord ++ tailWord_1876063) baseStart_1876063 baseEnd_1876063 := by
    simpa [prefixWord, tailWord_1876063, baseEnd_1876063] using wordTrace_append hprefix tailTrace_1876063
  have hstable : (prefixWord ++ tailWord_1876063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876063).length < 2 ^ (prefixWord ++ tailWord_1876063).sum := by decide
  have hdescent : baseEnd_1876063 < baseStart_1876063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876127 : List Nat := [1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1876127 : Nat := 118140960795 + 1876127 * 2 ^ 59
def prefixEnd_1876127 : Nat := 4983230072969 + 3 ^ 40 * 1876127 * 2
def baseEnd_1876127 : Nat := 963354919877886378184355

theorem tailTrace_1876127 : CollatzResearch.WordTrace tailWord_1876127 prefixEnd_1876127 963354919877886378184355 := by
  unfold tailWord_1876127
  simp only [CollatzResearch.WordTrace]
  refine ⟨68427973274119770827010635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45618648849413180551340423 68427973274119770827010635)
  ·
    refine ⟨102641959911179656240515953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68427973274119770827010635 102641959911179656240515953)
    ·
      refine ⟨76981469933384742180386965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102641959911179656240515953 76981469933384742180386965)
      ·
        refine ⟨3608506403127409789705639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76981469933384742180386965 3608506403127409789705639)
        ·
          refine ⟨5412759604691114684558459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608506403127409789705639 5412759604691114684558459)
          ·
            refine ⟨8119139407036672026837689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412759604691114684558459 8119139407036672026837689)
            ·
              refine ⟨6089354555277504020128267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8119139407036672026837689 6089354555277504020128267)
              ·
                refine ⟨9134031832916256030192401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089354555277504020128267 9134031832916256030192401)
                ·
                  refine ⟨6850523874687192022644301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9134031832916256030192401 6850523874687192022644301)
                  ·
                    refine ⟨2568946453007697008491613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6850523874687192022644301 2568946453007697008491613)
                    ·
                      refine ⟨963354919877886378184355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2568946453007697008491613 963354919877886378184355)
                      ·
                        rfl

theorem cell23_1876127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1876127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876127 prefixEnd_1876127 := by exact prefixLift 1876127
  have htrace : WordTrace (prefixWord ++ tailWord_1876127) baseStart_1876127 baseEnd_1876127 := by
    simpa [prefixWord, tailWord_1876127, baseEnd_1876127] using wordTrace_append hprefix tailTrace_1876127
  have hstable : (prefixWord ++ tailWord_1876127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876127).length < 2 ^ (prefixWord ++ tailWord_1876127).sum := by decide
  have hdescent : baseEnd_1876127 < baseStart_1876127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876143 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 10]
def baseStart_1876143 : Nat := 118140960795 + 1876143 * 2 ^ 59
def prefixEnd_1876143 : Nat := 4983230072969 + 3 ^ 40 * 1876143 * 2
def baseEnd_1876143 : Nat := 321121045189452771861427

theorem tailTrace_1876143 : CollatzResearch.WordTrace tailWord_1876143 prefixEnd_1876143 321121045189452771861427 := by
  unfold tailWord_1876143
  simp only [CollatzResearch.WordTrace]
  refine ⟨68428556842061805559593083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45619037894707870373062055 68428556842061805559593083)
  ·
    refine ⟨102642835263092708339389625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68428556842061805559593083 102642835263092708339389625)
    ·
      refine ⟨76982126447319531254542219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102642835263092708339389625 76982126447319531254542219)
      ·
        refine ⟨115473189670979296881813329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76982126447319531254542219 115473189670979296881813329)
        ·
          refine ⟨86604892253234472661359997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115473189670979296881813329 86604892253234472661359997)
          ·
            refine ⟨32476834594962927248009999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86604892253234472661359997 32476834594962927248009999)
            ·
              refine ⟨48715251892444390872014999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32476834594962927248009999 48715251892444390872014999)
              ·
                refine ⟨73072877838666586308022499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48715251892444390872014999 73072877838666586308022499)
                ·
                  refine ⟨109609316757999879462033749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73072877838666586308022499 109609316757999879462033749)
                  ·
                    refine ⟨321121045189452771861427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 109609316757999879462033749 321121045189452771861427)
                    ·
                      rfl

theorem cell23_1876143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 10].length) (baseStart_1876143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876143 prefixEnd_1876143 := by exact prefixLift 1876143
  have htrace : WordTrace (prefixWord ++ tailWord_1876143) baseStart_1876143 baseEnd_1876143 := by
    simpa [prefixWord, tailWord_1876143, baseEnd_1876143] using wordTrace_append hprefix tailTrace_1876143
  have hstable : (prefixWord ++ tailWord_1876143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876143).length < 2 ^ (prefixWord ++ tailWord_1876143).sum := by decide
  have hdescent : baseEnd_1876143 < baseStart_1876143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876177 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 3, 4]
def baseStart_1876177 : Nat := 118140960795 + 1876177 * 2 ^ 59
def prefixEnd_1876177 : Nat := 4983230072969 + 3 ^ 40 * 1876177 * 2
def baseEnd_1876177 : Nat := 321126864636870394186375

theorem tailTrace_1876177 : CollatzResearch.WordTrace tailWord_1876177 prefixEnd_1876177 321126864636870394186375 := by
  unfold tailWord_1876177
  simp only [CollatzResearch.WordTrace]
  refine ⟨68429796923938629366330785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45619864615959086244220523 68429796923938629366330785)
  ·
    refine ⟨51322347692953972024748089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68429796923938629366330785 51322347692953972024748089)
    ·
      refine ⟨38491760769715479018561067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51322347692953972024748089 38491760769715479018561067)
      ·
        refine ⟨57737641154573218527841601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38491760769715479018561067 57737641154573218527841601)
        ·
          refine ⟨43303230865929913895881201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57737641154573218527841601 43303230865929913895881201)
          ·
            refine ⟨32477423149447435421910901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43303230865929913895881201 32477423149447435421910901)
            ·
              refine ⟨3044758420260697070804147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32477423149447435421910901 3044758420260697070804147)
              ·
                refine ⟨4567137630391045606206221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044758420260697070804147 4567137630391045606206221)
                ·
                  refine ⟨1712676611396642102327333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4567137630391045606206221 1712676611396642102327333)
                  ·
                    refine ⟨321126864636870394186375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712676611396642102327333 321126864636870394186375)
                    ·
                      rfl

theorem cell23_1876177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_1876177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876177 prefixEnd_1876177 := by exact prefixLift 1876177
  have htrace : WordTrace (prefixWord ++ tailWord_1876177) baseStart_1876177 baseEnd_1876177 := by
    simpa [prefixWord, tailWord_1876177, baseEnd_1876177] using wordTrace_append hprefix tailTrace_1876177
  have hstable : (prefixWord ++ tailWord_1876177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876177).length < 2 ^ (prefixWord ++ tailWord_1876177).sum := by decide
  have hdescent : baseEnd_1876177 < baseStart_1876177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876217 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 3]
def baseStart_1876217 : Nat := 118140960795 + 1876217 * 2 ^ 59
def prefixEnd_1876217 : Nat := 4983230072969 + 3 ^ 40 * 1876217 * 2
def baseEnd_1876217 : Nat := 963401133136791026058941

theorem tailTrace_1876217 : CollatzResearch.WordTrace tailWord_1876217 prefixEnd_1876217 963401133136791026058941 := by
  unfold tailWord_1876217
  simp only [CollatzResearch.WordTrace]
  refine ⟨68431255843793716197786905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45620837229195810798524603 68431255843793716197786905)
  ·
    refine ⟨51323441882845287148340179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68431255843793716197786905 51323441882845287148340179)
    ·
      refine ⟨76985162824267930722510269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51323441882845287148340179 76985162824267930722510269)
      ·
        refine ⟨28869436059100474020941351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76985162824267930722510269 28869436059100474020941351)
        ·
          refine ⟨43304154088650711031412027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28869436059100474020941351 43304154088650711031412027)
          ·
            refine ⟨64956231132976066547118041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43304154088650711031412027 64956231132976066547118041)
            ·
              refine ⟨48717173349732049910338531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64956231132976066547118041 48717173349732049910338531)
              ·
                refine ⟨73075760024598074865507797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48717173349732049910338531 73075760024598074865507797)
                ·
                  refine ⟨1712713125576517379660339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 73075760024598074865507797 1712713125576517379660339)
                  ·
                    refine ⟨2569069688364776069490509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712713125576517379660339 2569069688364776069490509)
                    ·
                      refine ⟨963401133136791026058941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569069688364776069490509 963401133136791026058941)
                      ·
                        rfl

theorem cell23_1876217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7, 1, 3].length) (baseStart_1876217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876217 prefixEnd_1876217 := by exact prefixLift 1876217
  have htrace : WordTrace (prefixWord ++ tailWord_1876217) baseStart_1876217 baseEnd_1876217 := by
    simpa [prefixWord, tailWord_1876217, baseEnd_1876217] using wordTrace_append hprefix tailTrace_1876217
  have hstable : (prefixWord ++ tailWord_1876217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876217).length < 2 ^ (prefixWord ++ tailWord_1876217).sum := by decide
  have hdescent : baseEnd_1876217 < baseStart_1876217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876257 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1876257 : Nat := 118140960795 + 1876257 * 2 ^ 59
def prefixEnd_1876257 : Nat := 4983230072969 + 3 ^ 40 * 1876257 * 2
def baseEnd_1876257 : Nat := 963421672362970869558757

theorem tailTrace_1876257 : CollatzResearch.WordTrace tailWord_1876257 prefixEnd_1876257 963421672362970869558757 := by
  unfold tailWord_1876257
  simp only [CollatzResearch.WordTrace]
  refine ⟨68432714763648803029243025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45621809842432535352828683 68432714763648803029243025)
  ·
    refine ⟨51324536072736602271932269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68432714763648803029243025 51324536072736602271932269)
    ·
      refine ⟨19246701027276225851974601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51324536072736602271932269 19246701027276225851974601)
      ·
        refine ⟨14435025770457169388980951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19246701027276225851974601 14435025770457169388980951)
        ·
          refine ⟨21652538655685754083471427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14435025770457169388980951 21652538655685754083471427)
          ·
            refine ⟨32478807983528631125207141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21652538655685754083471427 32478807983528631125207141)
            ·
              refine ⟨6089776496911618335976339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32478807983528631125207141 6089776496911618335976339)
              ·
                refine ⟨9134664745367427503964509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6089776496911618335976339 9134664745367427503964509)
                ·
                  refine ⟨3425499279512785313986691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9134664745367427503964509 3425499279512785313986691)
                  ·
                    refine ⟨5138248919269177970980037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3425499279512785313986691 5138248919269177970980037)
                    ·
                      refine ⟨963421672362970869558757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5138248919269177970980037 963421672362970869558757)
                      ·
                        rfl

theorem cell23_1876257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1876257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876257 prefixEnd_1876257 := by exact prefixLift 1876257
  have htrace : WordTrace (prefixWord ++ tailWord_1876257) baseStart_1876257 baseEnd_1876257 := by
    simpa [prefixWord, tailWord_1876257, baseEnd_1876257] using wordTrace_append hprefix tailTrace_1876257
  have hstable : (prefixWord ++ tailWord_1876257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876257).length < 2 ^ (prefixWord ++ tailWord_1876257).sum := by decide
  have hdescent : baseEnd_1876257 < baseStart_1876257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876277 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1876277 : Nat := 118140960795 + 1876277 * 2 ^ 59
def prefixEnd_1876277 : Nat := 4983230072969 + 3 ^ 40 * 1876277 * 2
def baseEnd_1876277 : Nat := 963431941976060791308665

theorem tailTrace_1876277 : CollatzResearch.WordTrace tailWord_1876277 prefixEnd_1876277 963431941976060791308665 := by
  unfold tailWord_1876277
  simp only [CollatzResearch.WordTrace]
  refine ⟨68433444223576346444971085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45622296149050897629980723 68433444223576346444971085)
  ·
    refine ⟨25662541583841129916864157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68433444223576346444971085 25662541583841129916864157)
    ·
      refine ⟨9623453093940423718824059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25662541583841129916864157 9623453093940423718824059)
      ·
        refine ⟨14435179640910635578236089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9623453093940423718824059 14435179640910635578236089)
        ·
          refine ⟨10826384730682976683677067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14435179640910635578236089 10826384730682976683677067)
          ·
            refine ⟨16239577096024465025515601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826384730682976683677067 16239577096024465025515601)
            ·
              refine ⟨12179682822018348769136701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16239577096024465025515601 12179682822018348769136701)
              ·
                refine ⟨4567381058256880788426263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12179682822018348769136701 4567381058256880788426263)
                ·
                  refine ⟨6851071587385321182639395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567381058256880788426263 6851071587385321182639395)
                  ·
                    refine ⟨10276607381077981773959093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6851071587385321182639395 10276607381077981773959093)
                    ·
                      refine ⟨963431941976060791308665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10276607381077981773959093 963431941976060791308665)
                      ·
                        rfl

theorem cell23_1876277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1876277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876277 prefixEnd_1876277 := by exact prefixLift 1876277
  have htrace : WordTrace (prefixWord ++ tailWord_1876277) baseStart_1876277 baseEnd_1876277 := by
    simpa [prefixWord, tailWord_1876277, baseEnd_1876277] using wordTrace_append hprefix tailTrace_1876277
  have hstable : (prefixWord ++ tailWord_1876277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876277).length < 2 ^ (prefixWord ++ tailWord_1876277).sum := by decide
  have hdescent : baseEnd_1876277 < baseStart_1876277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876304 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4]
def baseStart_1876304 : Nat := 118140960795 + 1876304 * 2 ^ 59
def prefixEnd_1876304 : Nat := 4983230072969 + 3 ^ 40 * 1876304 * 2
def baseEnd_1876304 : Nat := 963445805953732185671041

theorem tailTrace_1876304 : CollatzResearch.WordTrace tailWord_1876304 prefixEnd_1876304 963445805953732185671041 := by
  unfold tailWord_1876304
  simp only [CollatzResearch.WordTrace]
  refine ⟨34217214497239265028101983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45622952662985686704135977 34217214497239265028101983)
  ·
    refine ⟨51325821745858897542152975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34217214497239265028101983 51325821745858897542152975)
    ·
      refine ⟨76988732618788346313229463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51325821745858897542152975 76988732618788346313229463)
      ·
        refine ⟨115483098928182519469844195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76988732618788346313229463 115483098928182519469844195)
        ·
          refine ⟨173224648392273779204766293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115483098928182519469844195 173224648392273779204766293)
          ·
            refine ⟨2029976348346958350055855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 173224648392273779204766293 2029976348346958350055855)
            ·
              refine ⟨3044964522520437525083783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029976348346958350055855 3044964522520437525083783)
              ·
                refine ⟨4567446783780656287625675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044964522520437525083783 4567446783780656287625675)
                ·
                  refine ⟨6851170175670984431438513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567446783780656287625675 6851170175670984431438513)
                  ·
                    refine ⟨5138377631753238323578885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6851170175670984431438513 5138377631753238323578885)
                    ·
                      refine ⟨963445805953732185671041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5138377631753238323578885 963445805953732185671041)
                      ·
                        rfl

theorem cell23_1876304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 4].length) (baseStart_1876304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876304 prefixEnd_1876304 := by exact prefixLift 1876304
  have htrace : WordTrace (prefixWord ++ tailWord_1876304) baseStart_1876304 baseEnd_1876304 := by
    simpa [prefixWord, tailWord_1876304, baseEnd_1876304] using wordTrace_append hprefix tailTrace_1876304
  have hstable : (prefixWord ++ tailWord_1876304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876304).length < 2 ^ (prefixWord ++ tailWord_1876304).sum := by decide
  have hdescent : baseEnd_1876304 < baseStart_1876304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876307 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3]
def baseStart_1876307 : Nat := 118140960795 + 1876307 * 2 ^ 59
def prefixEnd_1876307 : Nat := 4983230072969 + 3 ^ 40 * 1876307 * 2
def baseEnd_1876307 : Nat := 963447346395695673933527

theorem tailTrace_1876307 : CollatzResearch.WordTrace tailWord_1876307 prefixEnd_1876307 963447346395695673933527 := by
  unfold tailWord_1876307
  simp only [CollatzResearch.WordTrace]
  refine ⟨68434538413467661568563175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45623025608978441045708783 68434538413467661568563175)
  ·
    refine ⟨102651807620201492352844763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68434538413467661568563175 102651807620201492352844763)
    ·
      refine ⟨153977711430302238529267145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102651807620201492352844763 153977711430302238529267145)
      ·
        refine ⟨115483283572726678896950359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153977711430302238529267145 115483283572726678896950359)
        ·
          refine ⟨173224925359090018345425539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115483283572726678896950359 173224925359090018345425539)
          ·
            refine ⟨259837388038635027518138309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173224925359090018345425539 259837388038635027518138309)
            ·
              refine ⟨48719510257244067659650933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 259837388038635027518138309 48719510257244067659650933)
              ·
                refine ⟨4567454086616631343092275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48719510257244067659650933 4567454086616631343092275)
                ·
                  refine ⟨6851181129924947014638413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4567454086616631343092275 6851181129924947014638413)
                  ·
                    refine ⟨2569192923721855130489405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6851181129924947014638413 2569192923721855130489405)
                    ·
                      refine ⟨963447346395695673933527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569192923721855130489405 963447346395695673933527)
                      ·
                        rfl

theorem cell23_1876307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 3, 3].length) (baseStart_1876307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876307 prefixEnd_1876307 := by exact prefixLift 1876307
  have htrace : WordTrace (prefixWord ++ tailWord_1876307) baseStart_1876307 baseEnd_1876307 := by
    simpa [prefixWord, tailWord_1876307, baseEnd_1876307] using wordTrace_append hprefix tailTrace_1876307
  have hstable : (prefixWord ++ tailWord_1876307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876307).length < 2 ^ (prefixWord ++ tailWord_1876307).sum := by decide
  have hdescent : baseEnd_1876307 < baseStart_1876307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876324 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_1876324 : Nat := 118140960795 + 1876324 * 2 ^ 59
def prefixEnd_1876324 : Nat := 4983230072969 + 3 ^ 40 * 1876324 * 2
def baseEnd_1876324 : Nat := 963456075566822107420949

theorem tailTrace_1876324 : CollatzResearch.WordTrace tailWord_1876324 prefixEnd_1876324 963456075566822107420949 := by
  unfold tailWord_1876324
  simp only [CollatzResearch.WordTrace]
  refine ⟨34217579227203036735966013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45623438969604048981288017 34217579227203036735966013)
  ·
    refine ⟨12831592210201138775987255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34217579227203036735966013 12831592210201138775987255)
    ·
      refine ⟨19247388315301708163980883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12831592210201138775987255 19247388315301708163980883)
      ·
        refine ⟨28871082472952562245971325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19247388315301708163980883 28871082472952562245971325)
        ·
          refine ⟨10826655927357210842239247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28871082472952562245971325 10826655927357210842239247)
          ·
            refine ⟨16239983891035816263358871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10826655927357210842239247 16239983891035816263358871)
            ·
              refine ⟨24359975836553724395038307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16239983891035816263358871 24359975836553724395038307)
              ·
                refine ⟨36539963754830586592557461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24359975836553724395038307 36539963754830586592557461)
                ·
                  refine ⟨1712810801007683746526131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36539963754830586592557461 1712810801007683746526131)
                  ·
                    refine ⟨2569216201511525619789197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712810801007683746526131 2569216201511525619789197)
                    ·
                      refine ⟨963456075566822107420949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569216201511525619789197 963456075566822107420949)
                      ·
                        rfl

theorem cell23_1876324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_1876324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876324 prefixEnd_1876324 := by exact prefixLift 1876324
  have htrace : WordTrace (prefixWord ++ tailWord_1876324) baseStart_1876324 baseEnd_1876324 := by
    simpa [prefixWord, tailWord_1876324, baseEnd_1876324] using wordTrace_append hprefix tailTrace_1876324
  have hstable : (prefixWord ++ tailWord_1876324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876324).length < 2 ^ (prefixWord ++ tailWord_1876324).sum := by decide
  have hdescent : baseEnd_1876324 < baseStart_1876324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876325 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 1, 2, 2]
def baseStart_1876325 : Nat := 118140960795 + 1876325 * 2 ^ 59
def prefixEnd_1876325 : Nat := 4983230072969 + 3 ^ 40 * 1876325 * 2
def baseEnd_1876325 : Nat := 963456589047476603508445

theorem tailTrace_1876325 : CollatzResearch.WordTrace tailWord_1876325 prefixEnd_1876325 963456589047476603508445 := by
  unfold tailWord_1876325
  simp only [CollatzResearch.WordTrace]
  refine ⟨68435194927402450642718429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45623463284934967095145619 68435194927402450642718429)
  ·
    refine ⟨25663198097775918991019411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68435194927402450642718429 25663198097775918991019411)
    ·
      refine ⟨38494797146663878486529117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25663198097775918991019411 38494797146663878486529117)
      ·
        refine ⟨14435548929998954432448419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38494797146663878486529117 14435548929998954432448419)
        ·
          refine ⟨21653323394998431648672629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14435548929998954432448419 21653323394998431648672629)
          ·
            refine ⟨2029999068281102967063059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21653323394998431648672629 2029999068281102967063059)
            ·
              refine ⟨3044998602421654450594589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029999068281102967063059 3044998602421654450594589)
              ·
                refine ⟨1141874475908120418972971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3044998602421654450594589 1141874475908120418972971)
                ·
                  refine ⟨1712811713862180628459457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141874475908120418972971 1712811713862180628459457)
                  ·
                    refine ⟨1284608785396635471344593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1712811713862180628459457 1284608785396635471344593)
                    ·
                      refine ⟨963456589047476603508445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284608785396635471344593 963456589047476603508445)
                      ·
                        rfl

theorem cell23_1876325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_1876325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876325 prefixEnd_1876325 := by exact prefixLift 1876325
  have htrace : WordTrace (prefixWord ++ tailWord_1876325) baseStart_1876325 baseEnd_1876325 := by
    simpa [prefixWord, tailWord_1876325, baseEnd_1876325] using wordTrace_append hprefix tailTrace_1876325
  have hstable : (prefixWord ++ tailWord_1876325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876325).length < 2 ^ (prefixWord ++ tailWord_1876325).sum := by decide
  have hdescent : baseEnd_1876325 < baseStart_1876325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876341 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1876341 : Nat := 118140960795 + 1876341 * 2 ^ 59
def prefixEnd_1876341 : Nat := 4983230072969 + 3 ^ 40 * 1876341 * 2
def baseEnd_1876341 : Nat := 963464804737948540908371

theorem tailTrace_1876341 : CollatzResearch.WordTrace tailWord_1876341 prefixEnd_1876341 963464804737948540908371 := by
  unfold tailWord_1876341
  simp only [CollatzResearch.WordTrace]
  refine ⟨68435778495344485375300877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45623852330229656916867251 68435778495344485375300877)
  ·
    refine ⟨25663416935754182015737829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68435778495344485375300877 25663416935754182015737829)
    ·
      refine ⟨4811890675453909127950843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25663416935754182015737829 4811890675453909127950843)
      ·
        refine ⟨7217836013180863691926265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811890675453909127950843 7217836013180863691926265)
        ·
          refine ⟨5413377009885647768944699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7217836013180863691926265 5413377009885647768944699)
          ·
            refine ⟨8120065514828471653417049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413377009885647768944699 8120065514828471653417049)
            ·
              refine ⟨6090049136121353740062787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120065514828471653417049 6090049136121353740062787)
              ·
                refine ⟨9135073704182030610094181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090049136121353740062787 9135073704182030610094181)
                ·
                  refine ⟨1712826319534130739392659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9135073704182030610094181 1712826319534130739392659)
                  ·
                    refine ⟨2569239479301196109088989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1712826319534130739392659 2569239479301196109088989)
                    ·
                      refine ⟨963464804737948540908371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569239479301196109088989 963464804737948540908371)
                      ·
                        rfl

theorem cell23_1876341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1876341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876341 prefixEnd_1876341 := by exact prefixLift 1876341
  have htrace : WordTrace (prefixWord ++ tailWord_1876341) baseStart_1876341 baseEnd_1876341 := by
    simpa [prefixWord, tailWord_1876341, baseEnd_1876341] using wordTrace_append hprefix tailTrace_1876341
  have hstable : (prefixWord ++ tailWord_1876341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876341).length < 2 ^ (prefixWord ++ tailWord_1876341).sum := by decide
  have hdescent : baseEnd_1876341 < baseStart_1876341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876342 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1876342 : Nat := 118140960795 + 1876342 * 2 ^ 59
def prefixEnd_1876342 : Nat := 4983230072969 + 3 ^ 40 * 1876342 * 2
def baseEnd_1876342 : Nat := 963465318218603036995867

theorem tailTrace_1876342 : CollatzResearch.WordTrace tailWord_1876342 prefixEnd_1876342 963465318218603036995867 := by
  unfold tailWord_1876342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277238435521303909130455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45623876645560575030724853 4277238435521303909130455)
  ·
    refine ⟨6415857653281955863695683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277238435521303909130455 6415857653281955863695683)
    ·
      refine ⟨9623786479922933795543525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415857653281955863695683 9623786479922933795543525)
      ·
        refine ⟨1804459964985550086664411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9623786479922933795543525 1804459964985550086664411)
        ·
          refine ⟨2706689947478325129996617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804459964985550086664411 2706689947478325129996617)
          ·
            refine ⟨2030017460608743847497463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706689947478325129996617 2030017460608743847497463)
            ·
              refine ⟨3045026190913115771246195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030017460608743847497463 3045026190913115771246195)
              ·
                refine ⟨4567539286369673656869293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045026190913115771246195 4567539286369673656869293)
                ·
                  refine ⟨1712827232388627621325985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4567539286369673656869293 1712827232388627621325985)
                  ·
                    refine ⟨1284620424291470715994489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1712827232388627621325985 1284620424291470715994489)
                    ·
                      refine ⟨963465318218603036995867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284620424291470715994489 963465318218603036995867)
                      ·
                        rfl

theorem cell23_1876342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1876342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876342 prefixEnd_1876342 := by exact prefixLift 1876342
  have htrace : WordTrace (prefixWord ++ tailWord_1876342) baseStart_1876342 baseEnd_1876342 := by
    simpa [prefixWord, tailWord_1876342, baseEnd_1876342] using wordTrace_append hprefix tailTrace_1876342
  have hstable : (prefixWord ++ tailWord_1876342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876342).length < 2 ^ (prefixWord ++ tailWord_1876342).sum := by decide
  have hdescent : baseEnd_1876342 < baseStart_1876342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876414 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3]
def baseStart_1876414 : Nat := 118140960795 + 1876414 * 2 ^ 59
def prefixEnd_1876414 : Nat := 4983230072969 + 3 ^ 40 * 1876414 * 2
def baseEnd_1876414 : Nat := 963502288825726755295535

theorem tailTrace_1876414 : CollatzResearch.WordTrace tailWord_1876414 prefixEnd_1876414 963502288825726755295535 := by
  unfold tailWord_1876414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8554805128010002355338537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45625627349386679228472197 8554805128010002355338537)
  ·
    refine ⟨6416103846007501766503903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8554805128010002355338537 6416103846007501766503903)
    ·
      refine ⟨9624155769011252649755855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416103846007501766503903 9624155769011252649755855)
      ·
        refine ⟨14436233653516878974633783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624155769011252649755855 14436233653516878974633783)
        ·
          refine ⟨21654350480275318461950675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14436233653516878974633783 21654350480275318461950675)
          ·
            refine ⟨32481525720412977692926013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21654350480275318461950675 32481525720412977692926013)
            ·
              refine ⟨12180572145154866634847255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32481525720412977692926013 12180572145154866634847255)
              ·
                refine ⟨18270858217732299952270883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12180572145154866634847255 18270858217732299952270883)
                ·
                  refine ⟨27406287326598449928406325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18270858217732299952270883 27406287326598449928406325)
                  ·
                    refine ⟨2569339436868604680788093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27406287326598449928406325 2569339436868604680788093)
                    ·
                      refine ⟨963502288825726755295535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569339436868604680788093 963502288825726755295535)
                      ·
                        rfl

theorem cell23_1876414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_1876414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876414 prefixEnd_1876414 := by exact prefixLift 1876414
  have htrace : WordTrace (prefixWord ++ tailWord_1876414) baseStart_1876414 baseEnd_1876414 := by
    simpa [prefixWord, tailWord_1876414, baseEnd_1876414] using wordTrace_append hprefix tailTrace_1876414
  have hstable : (prefixWord ++ tailWord_1876414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876414).length < 2 ^ (prefixWord ++ tailWord_1876414).sum := by decide
  have hdescent : baseEnd_1876414 < baseStart_1876414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876438 : List Nat := [5, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1876438 : Nat := 118140960795 + 1876438 * 2 ^ 59
def prefixEnd_1876438 : Nat := 4983230072969 + 3 ^ 40 * 1876438 * 2
def baseEnd_1876438 : Nat := 107057179151270517932825

theorem tailTrace_1876438 : CollatzResearch.WordTrace tailWord_1876438 prefixEnd_1876438 107057179151270517932825 := by
  unfold tailWord_1876438
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277457273499566933848873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45626210917328713961054645 4277457273499566933848873)
  ·
    refine ⟨3208092955124675200386655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4277457273499566933848873 3208092955124675200386655)
    ·
      refine ⟨4812139432687012800579983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3208092955124675200386655 4812139432687012800579983)
      ·
        refine ⟨7218209149030519200869975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812139432687012800579983 7218209149030519200869975)
        ·
          refine ⟨10827313723545778801304963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218209149030519200869975 10827313723545778801304963)
          ·
            refine ⟨16240970585318668201957445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10827313723545778801304963 16240970585318668201957445)
            ·
              refine ⟨3045181984747250287867021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16240970585318668201957445 3045181984747250287867021)
              ·
                refine ⟨1141943244280218857950133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3045181984747250287867021 1141943244280218857950133)
                ·
                  refine ⟨107057179151270517932825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1141943244280218857950133 107057179151270517932825)
                  ·
                    rfl

theorem cell23_1876438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1876438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876438 prefixEnd_1876438 := by exact prefixLift 1876438
  have htrace : WordTrace (prefixWord ++ tailWord_1876438) baseStart_1876438 baseEnd_1876438 := by
    simpa [prefixWord, tailWord_1876438, baseEnd_1876438] using wordTrace_append hprefix tailTrace_1876438
  have hstable : (prefixWord ++ tailWord_1876438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876438).length < 2 ^ (prefixWord ++ tailWord_1876438).sum := by decide
  have hdescent : baseEnd_1876438 < baseStart_1876438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876467 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6]
def baseStart_1876467 : Nat := 118140960795 + 1876467 * 2 ^ 59
def prefixEnd_1876467 : Nat := 4983230072969 + 3 ^ 40 * 1876467 * 2
def baseEnd_1876467 : Nat := 963529503300415047932791

theorem tailTrace_1876467 : CollatzResearch.WordTrace tailWord_1876467 prefixEnd_1876467 963529503300415047932791 := by
  unfold tailWord_1876467
  simp only [CollatzResearch.WordTrace]
  refine ⟨68440374092888008894387655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45626916061925339262925103 68440374092888008894387655)
  ·
    refine ⟨102660561139332013341581483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68440374092888008894387655 102660561139332013341581483)
    ·
      refine ⟨153990841708998020012372225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102660561139332013341581483 153990841708998020012372225)
      ·
        refine ⟨115493131281748515009279169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153990841708998020012372225 115493131281748515009279169)
        ·
          refine ⟨86619848461311386256959377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115493131281748515009279169 86619848461311386256959377)
          ·
            refine ⟨64964886345983539692719533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86619848461311386256959377 64964886345983539692719533)
            ·
              refine ⟨24361832379743827384769825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64964886345983539692719533 24361832379743827384769825)
              ·
                refine ⟨18271374284807870538577369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24361832379743827384769825 18271374284807870538577369)
                ·
                  refine ⟨13703530713605902903933027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18271374284807870538577369 13703530713605902903933027)
                  ·
                    refine ⟨20555296070408854355899541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13703530713605902903933027 20555296070408854355899541)
                    ·
                      refine ⟨963529503300415047932791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20555296070408854355899541 963529503300415047932791)
                      ·
                        rfl

theorem cell23_1876467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 1, 6].length) (baseStart_1876467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876467 prefixEnd_1876467 := by exact prefixLift 1876467
  have htrace : WordTrace (prefixWord ++ tailWord_1876467) baseStart_1876467 baseEnd_1876467 := by
    simpa [prefixWord, tailWord_1876467, baseEnd_1876467] using wordTrace_append hprefix tailTrace_1876467
  have hstable : (prefixWord ++ tailWord_1876467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876467).length < 2 ^ (prefixWord ++ tailWord_1876467).sum := by decide
  have hdescent : baseEnd_1876467 < baseStart_1876467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876474 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3]
def baseStart_1876474 : Nat := 118140960795 + 1876474 * 2 ^ 59
def prefixEnd_1876474 : Nat := 4983230072969 + 3 ^ 40 * 1876474 * 2
def baseEnd_1876474 : Nat := 963533097664996520545259

theorem tailTrace_1876474 : CollatzResearch.WordTrace tailWord_1876474 prefixEnd_1876474 963533097664996520545259 := by
  unfold tailWord_1876474
  simp only [CollatzResearch.WordTrace]
  refine ⟨17110157350965662272473119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45627086269241766059928317 17110157350965662272473119)
  ·
    refine ⟨25665236026448493408709679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17110157350965662272473119 25665236026448493408709679)
    ·
      refine ⟨38497854039672740113064519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25665236026448493408709679 38497854039672740113064519)
      ·
        refine ⟨57746781059509110169596779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38497854039672740113064519 57746781059509110169596779)
        ·
          refine ⟨86620171589263665254395169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57746781059509110169596779 86620171589263665254395169)
          ·
            refine ⟨64965128691947748940796377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86620171589263665254395169 64965128691947748940796377)
            ·
              refine ⟨48723846518960811705597283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64965128691947748940796377 48723846518960811705597283)
              ·
                refine ⟨73085769778441217558395925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48723846518960811705597283 73085769778441217558395925)
                ·
                  refine ⟨3425895458364432073049809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73085769778441217558395925 3425895458364432073049809)
                  ·
                    refine ⟨2569421593773324054787357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3425895458364432073049809 2569421593773324054787357)
                    ·
                      refine ⟨963533097664996520545259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569421593773324054787357 963533097664996520545259)
                      ·
                        rfl

theorem cell23_1876474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 6, 2, 3].length) (baseStart_1876474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876474 prefixEnd_1876474 := by exact prefixLift 1876474
  have htrace : WordTrace (prefixWord ++ tailWord_1876474) baseStart_1876474 baseEnd_1876474 := by
    simpa [prefixWord, tailWord_1876474, baseEnd_1876474] using wordTrace_append hprefix tailTrace_1876474
  have hstable : (prefixWord ++ tailWord_1876474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876474).length < 2 ^ (prefixWord ++ tailWord_1876474).sum := by decide
  have hdescent : baseEnd_1876474 < baseStart_1876474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876481 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1876481 : Nat := 118140960795 + 1876481 * 2 ^ 59
def prefixEnd_1876481 : Nat := 4983230072969 + 3 ^ 40 * 1876481 * 2
def baseEnd_1876481 : Nat := 321178897343192664385909

theorem tailTrace_1876481 : CollatzResearch.WordTrace tailWord_1876481 prefixEnd_1876481 321178897343192664385909 := by
  unfold tailWord_1876481
  simp only [CollatzResearch.WordTrace]
  refine ⟨68440884714837289285397297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45627256476558192856931531 68440884714837289285397297)
  ·
    refine ⟨51330663536127966964047973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68440884714837289285397297 51330663536127966964047973)
    ·
      refine ⟨9624499413023993805758995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51330663536127966964047973 9624499413023993805758995)
      ·
        refine ⟨14436749119535990708638493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624499413023993805758995 14436749119535990708638493)
        ·
          refine ⟨5413780919825996515739435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14436749119535990708638493 5413780919825996515739435)
          ·
            refine ⟨8120671379738994773609153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413780919825996515739435 8120671379738994773609153)
            ·
              refine ⟨6090503534804246080206865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8120671379738994773609153 6090503534804246080206865)
              ·
                refine ⟨4567877651103184560155149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090503534804246080206865 4567877651103184560155149)
                ·
                  refine ⟨1712954119163694210058181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4567877651103184560155149 1712954119163694210058181)
                  ·
                    refine ⟨321178897343192664385909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712954119163694210058181 321178897343192664385909)
                    ·
                      rfl

theorem cell23_1876481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1876481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876481 prefixEnd_1876481 := by exact prefixLift 1876481
  have htrace : WordTrace (prefixWord ++ tailWord_1876481) baseStart_1876481 baseEnd_1876481 := by
    simpa [prefixWord, tailWord_1876481, baseEnd_1876481] using wordTrace_append hprefix tailTrace_1876481
  have hstable : (prefixWord ++ tailWord_1876481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876481).length < 2 ^ (prefixWord ++ tailWord_1876481).sum := by decide
  have hdescent : baseEnd_1876481 < baseStart_1876481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876494 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 8]
def baseStart_1876494 : Nat := 118140960795 + 1876494 * 2 ^ 59
def prefixEnd_1876494 : Nat := 4983230072969 + 3 ^ 40 * 1876494 * 2
def baseEnd_1876494 : Nat := 107060374142009604699463

theorem tailTrace_1876494 : CollatzResearch.WordTrace tailWord_1876494 prefixEnd_1876494 107060374142009604699463 := by
  unfold tailWord_1876494
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555169857973774063202567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45627572575860128337080357 8555169857973774063202567)
  ·
    refine ⟨12832754786960661094803851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8555169857973774063202567 12832754786960661094803851)
    ·
      refine ⟨19249132180440991642205777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12832754786960661094803851 19249132180440991642205777)
      ·
        refine ⟨14436849135330743731654333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19249132180440991642205777 14436849135330743731654333)
        ·
          refine ⟨5413818425749028899370375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14436849135330743731654333 5413818425749028899370375)
          ·
            refine ⟨8120727638623543349055563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413818425749028899370375 8120727638623543349055563)
            ·
              refine ⟨12181091457935315023583345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8120727638623543349055563 12181091457935315023583345)
              ·
                refine ⟨9135818593451486267687509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12181091457935315023583345 9135818593451486267687509)
                ·
                  refine ⟨107060374142009604699463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9135818593451486267687509 107060374142009604699463)
                  ·
                    rfl

theorem cell23_1876494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 8].length) (baseStart_1876494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876494 prefixEnd_1876494 := by exact prefixLift 1876494
  have htrace : WordTrace (prefixWord ++ tailWord_1876494) baseStart_1876494 baseEnd_1876494 := by
    simpa [prefixWord, tailWord_1876494, baseEnd_1876494] using wordTrace_append hprefix tailTrace_1876494
  have hstable : (prefixWord ++ tailWord_1876494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876494).length < 2 ^ (prefixWord ++ tailWord_1876494).sum := by decide
  have hdescent : baseEnd_1876494 < baseStart_1876494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876497 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 8]
def baseStart_1876497 : Nat := 118140960795 + 1876497 * 2 ^ 59
def prefixEnd_1876497 : Nat := 4983230072969 + 3 ^ 40 * 1876497 * 2
def baseEnd_1876497 : Nat := 963544907720049930557653

theorem tailTrace_1876497 : CollatzResearch.WordTrace tailWord_1876497 prefixEnd_1876497 963544907720049930557653 := by
  unfold tailWord_1876497
  simp only [CollatzResearch.WordTrace]
  refine ⟨68441468282779324017979745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45627645521852882678653163 68441468282779324017979745)
  ·
    refine ⟨51331101212084493013484809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68441468282779324017979745 51331101212084493013484809)
    ·
      refine ⟨38498325909063369760113607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51331101212084493013484809 38498325909063369760113607)
      ·
        refine ⟨57747488863595054640170411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38498325909063369760113607 57747488863595054640170411)
        ·
          refine ⟨86621233295392581960255617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57747488863595054640170411 86621233295392581960255617)
          ·
            refine ⟨64965924971544436470191713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86621233295392581960255617 64965924971544436470191713)
            ·
              refine ⟨48724443728658327352643785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64965924971544436470191713 48724443728658327352643785)
              ·
                refine ⟨36543332796493745514482839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48724443728658327352643785 36543332796493745514482839)
                ·
                  refine ⟨54814999194740618271724259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36543332796493745514482839 54814999194740618271724259)
                  ·
                    refine ⟨82222498792110927407586389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54814999194740618271724259 82222498792110927407586389)
                    ·
                      refine ⟨963544907720049930557653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 82222498792110927407586389 963544907720049930557653)
                      ·
                        rfl

theorem cell23_1876497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_1876497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876497 prefixEnd_1876497 := by exact prefixLift 1876497
  have htrace : WordTrace (prefixWord ++ tailWord_1876497) baseStart_1876497 baseEnd_1876497 := by
    simpa [prefixWord, tailWord_1876497, baseEnd_1876497] using wordTrace_append hprefix tailTrace_1876497
  have hstable : (prefixWord ++ tailWord_1876497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876497).length < 2 ^ (prefixWord ++ tailWord_1876497).sum := by decide
  have hdescent : baseEnd_1876497 < baseStart_1876497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876515 : List Nat := [1, 1, 1, 4, 4, 2, 3, 2, 1, 4]
def baseStart_1876515 : Nat := 118140960795 + 1876515 * 2 ^ 59
def prefixEnd_1876515 : Nat := 4983230072969 + 3 ^ 40 * 1876515 * 2
def baseEnd_1876515 : Nat := 321184716790610286710857

theorem tailTrace_1876515 : CollatzResearch.WordTrace tailWord_1876515 prefixEnd_1876515 321184716790610286710857 := by
  unfold tailWord_1876515
  simp only [CollatzResearch.WordTrace]
  refine ⟨68442124796714113092134999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45628083197809408728089999 68442124796714113092134999)
  ·
    refine ⟨102663187195071169638202499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68442124796714113092134999 102663187195071169638202499)
    ·
      refine ⟨153994780792606754457303749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102663187195071169638202499 153994780792606754457303749)
      ·
        refine ⟨28874021398613766460744453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153994780792606754457303749 28874021398613766460744453)
        ·
          refine ⟨5413879012240081211389585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28874021398613766460744453 5413879012240081211389585)
          ·
            refine ⟨4060409259180060908542189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5413879012240081211389585 4060409259180060908542189)
            ·
              refine ⟨1522653472192522840703321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060409259180060908542189 1522653472192522840703321)
              ·
                refine ⟨1141990104144392130527491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522653472192522840703321 1141990104144392130527491)
                ·
                  refine ⟨1712985156216588195791237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1141990104144392130527491 1712985156216588195791237)
                  ·
                    refine ⟨321184716790610286710857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1712985156216588195791237 321184716790610286710857)
                    ·
                      rfl

theorem cell23_1876515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 1, 4].length) (baseStart_1876515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876515 prefixEnd_1876515 := by exact prefixLift 1876515
  have htrace : WordTrace (prefixWord ++ tailWord_1876515) baseStart_1876515 baseEnd_1876515 := by
    simpa [prefixWord, tailWord_1876515, baseEnd_1876515] using wordTrace_append hprefix tailTrace_1876515
  have hstable : (prefixWord ++ tailWord_1876515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876515).length < 2 ^ (prefixWord ++ tailWord_1876515).sum := by decide
  have hdescent : baseEnd_1876515 < baseStart_1876515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876527 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10]
def baseStart_1876527 : Nat := 118140960795 + 1876527 * 2 ^ 59
def prefixEnd_1876527 : Nat := 4983230072969 + 3 ^ 40 * 1876527 * 2
def baseEnd_1876527 : Nat := 963560312139684813182515

theorem tailTrace_1876527 : CollatzResearch.WordTrace tailWord_1876527 prefixEnd_1876527 963560312139684813182515 := by
  unfold tailWord_1876527
  simp only [CollatzResearch.WordTrace]
  refine ⟨68442562472670639141571835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45628374981780426094381223 68442562472670639141571835)
  ·
    refine ⟨102663843709005958712357753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68442562472670639141571835 102663843709005958712357753)
    ·
      refine ⟨76997882781754469034268315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102663843709005958712357753 76997882781754469034268315)
      ·
        refine ⟨115496824172631703551402473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76997882781754469034268315 115496824172631703551402473)
        ·
          refine ⟨86622618129473777663551855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115496824172631703551402473 86622618129473777663551855)
          ·
            refine ⟨129933927194210666495327783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86622618129473777663551855 129933927194210666495327783)
            ·
              refine ⟨194900890791315999742991675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129933927194210666495327783 194900890791315999742991675)
              ·
                refine ⟨292351336186973999614487513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 194900890791315999742991675 292351336186973999614487513)
                ·
                  refine ⟨219263502140230499710865635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 292351336186973999614487513 219263502140230499710865635)
                  ·
                    refine ⟨328895253210345749566298453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 219263502140230499710865635 328895253210345749566298453)
                    ·
                      refine ⟨963560312139684813182515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 328895253210345749566298453 963560312139684813182515)
                      ·
                        rfl

theorem cell23_1876527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 10].length) (baseStart_1876527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876527 prefixEnd_1876527 := by exact prefixLift 1876527
  have htrace : WordTrace (prefixWord ++ tailWord_1876527) baseStart_1876527 baseEnd_1876527 := by
    simpa [prefixWord, tailWord_1876527, baseEnd_1876527] using wordTrace_append hprefix tailTrace_1876527
  have hstable : (prefixWord ++ tailWord_1876527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876527).length < 2 ^ (prefixWord ++ tailWord_1876527).sum := by decide
  have hdescent : baseEnd_1876527 < baseStart_1876527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876531 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 4, 3, 2]
def baseStart_1876531 : Nat := 118140960795 + 1876531 * 2 ^ 59
def prefixEnd_1876531 : Nat := 4983230072969 + 3 ^ 40 * 1876531 * 2
def baseEnd_1876531 : Nat := 963562366062302797532497

theorem tailTrace_1876531 : CollatzResearch.WordTrace tailWord_1876531 prefixEnd_1876531 963562366062302797532497 := by
  unfold tailWord_1876531
  simp only [CollatzResearch.WordTrace]
  refine ⟨68442708364656147824717447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45628472243104098549811631 68442708364656147824717447)
  ·
    refine ⟨102664062546984221737076171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68442708364656147824717447 102664062546984221737076171)
    ·
      refine ⟨153996093820476332605614257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102664062546984221737076171 153996093820476332605614257)
      ·
        refine ⟨115497070365357249454210693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153996093820476332605614257 115497070365357249454210693)
        ·
          refine ⟨21655700693504484272664505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115497070365357249454210693 21655700693504484272664505)
          ·
            refine ⟨16241775520128363204498379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21655700693504484272664505 16241775520128363204498379)
            ·
              refine ⟨24362663280192544806747569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16241775520128363204498379 24362663280192544806747569)
              ·
                refine ⟨18271997460144408605060677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24362663280192544806747569 18271997460144408605060677)
                ·
                  refine ⟨3425999523777076613448877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18271997460144408605060677 3425999523777076613448877)
                  ·
                    refine ⟨1284749821416403730043329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3425999523777076613448877 1284749821416403730043329)
                    ·
                      refine ⟨963562366062302797532497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284749821416403730043329 963562366062302797532497)
                      ·
                        rfl

theorem cell23_1876531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 3, 2].length) (baseStart_1876531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876531 prefixEnd_1876531 := by exact prefixLift 1876531
  have htrace : WordTrace (prefixWord ++ tailWord_1876531) baseStart_1876531 baseEnd_1876531 := by
    simpa [prefixWord, tailWord_1876531, baseEnd_1876531] using wordTrace_append hprefix tailTrace_1876531
  have hstable : (prefixWord ++ tailWord_1876531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876531).length < 2 ^ (prefixWord ++ tailWord_1876531).sum := by decide
  have hdescent : baseEnd_1876531 < baseStart_1876531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876541 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 3, 5]
def baseStart_1876541 : Nat := 118140960795 + 1876541 * 2 ^ 59
def prefixEnd_1876541 : Nat := 4983230072969 + 3 ^ 40 * 1876541 * 2
def baseEnd_1876541 : Nat := 321189166956282586135817

theorem tailTrace_1876541 : CollatzResearch.WordTrace tailWord_1876541 prefixEnd_1876541 321189166956282586135817 := by
  unfold tailWord_1876541
  simp only [CollatzResearch.WordTrace]
  refine ⟨68443073094619919532581477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45628715396413279688387651 68443073094619919532581477)
  ·
    refine ⟨12833076205241234912359027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68443073094619919532581477 12833076205241234912359027)
    ·
      refine ⟨19249614307861852368538541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833076205241234912359027 19249614307861852368538541)
      ·
        refine ⟨7218605365448194638201953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19249614307861852368538541 7218605365448194638201953)
        ·
          refine ⟨5413954024086145978651465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7218605365448194638201953 5413954024086145978651465)
          ·
            refine ⟨4060465518064609483988599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5413954024086145978651465 4060465518064609483988599)
            ·
              refine ⟨6090698277096914225982899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060465518064609483988599 6090698277096914225982899)
              ·
                refine ⟨9136047415645371338974349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090698277096914225982899 9136047415645371338974349)
                ·
                  refine ⟨3426017780867014252115381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9136047415645371338974349 3426017780867014252115381)
                  ·
                    refine ⟨321189166956282586135817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3426017780867014252115381 321189166956282586135817)
                    ·
                      rfl

theorem cell23_1876541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_1876541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876541 prefixEnd_1876541 := by exact prefixLift 1876541
  have htrace : WordTrace (prefixWord ++ tailWord_1876541) baseStart_1876541 baseEnd_1876541 := by
    simpa [prefixWord, tailWord_1876541, baseEnd_1876541] using wordTrace_append hprefix tailTrace_1876541
  have hstable : (prefixWord ++ tailWord_1876541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876541).length < 2 ^ (prefixWord ++ tailWord_1876541).sum := by decide
  have hdescent : baseEnd_1876541 < baseStart_1876541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876554 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 3, 6]
def baseStart_1876554 : Nat := 118140960795 + 1876554 * 2 ^ 59
def prefixEnd_1876554 : Nat := 4983230072969 + 3 ^ 40 * 1876554 * 2
def baseEnd_1876554 : Nat := 321191392039118735848297

theorem tailTrace_1876554 : CollatzResearch.WordTrace tailWord_1876554 prefixEnd_1876554 321191392039118735848297 := by
  unfold tailWord_1876554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17110886810893205688201179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45629031495715215168536477 17110886810893205688201179)
  ·
    refine ⟨25666330216339808532301769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17110886810893205688201179 25666330216339808532301769)
    ·
      refine ⟨19249747662254856399226327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25666330216339808532301769 19249747662254856399226327)
      ·
        refine ⟨28874621493382284598839491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19249747662254856399226327 28874621493382284598839491)
        ·
          refine ⟨43311932240073426898259237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28874621493382284598839491 43311932240073426898259237)
          ·
            refine ⟨8120987295013767543423607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43311932240073426898259237 8120987295013767543423607)
            ·
              refine ⟨12181480942520651315135411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8120987295013767543423607 12181480942520651315135411)
              ·
                refine ⟨18272221413780976972703117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12181480942520651315135411 18272221413780976972703117)
                ·
                  refine ⟨6852083030167866364763669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18272221413780976972703117 6852083030167866364763669)
                  ·
                    refine ⟨321191392039118735848297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6852083030167866364763669 321191392039118735848297)
                    ·
                      rfl

theorem cell23_1876554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_1876554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876554 prefixEnd_1876554 := by exact prefixLift 1876554
  have htrace : WordTrace (prefixWord ++ tailWord_1876554) baseStart_1876554 baseEnd_1876554 := by
    simpa [prefixWord, tailWord_1876554, baseEnd_1876554] using wordTrace_append hprefix tailTrace_1876554
  have hstable : (prefixWord ++ tailWord_1876554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876554).length < 2 ^ (prefixWord ++ tailWord_1876554).sum := by decide
  have hdescent : baseEnd_1876554 < baseStart_1876554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876572 : List Nat := [2, 2, 4, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1876572 : Nat := 118140960795 + 1876572 * 2 ^ 59
def prefixEnd_1876572 : Nat := 4983230072969 + 3 ^ 40 * 1876572 * 2
def baseEnd_1876572 : Nat := 963583418769137137119809

theorem tailTrace_1876572 : CollatzResearch.WordTrace tailWord_1876572 prefixEnd_1876572 963583418769137137119809 := by
  unfold tailWord_1876572
  simp only [CollatzResearch.WordTrace]
  refine ⟨34222101878753805913479985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45629469171671741217973313 34222101878753805913479985)
  ·
    refine ⟨25666576409065354435109989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34222101878753805913479985 25666576409065354435109989)
    ·
      refine ⟨4812483076699753956583123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25666576409065354435109989 4812483076699753956583123)
      ·
        refine ⟨7218724615049630934874685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812483076699753956583123 7218724615049630934874685)
        ·
          refine ⟨2707021730643611600578007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7218724615049630934874685 2707021730643611600578007)
          ·
            refine ⟨4060532595965417400867011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707021730643611600578007 4060532595965417400867011)
            ·
              refine ⟨6090798893948126101300517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060532595965417400867011 6090798893948126101300517)
              ·
                refine ⟨1142024792615273643993847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6090798893948126101300517 1142024792615273643993847)
                ·
                  refine ⟨1713037188922910465990771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142024792615273643993847 1713037188922910465990771)
                  ·
                    refine ⟨2569555783384365698986157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713037188922910465990771 2569555783384365698986157)
                    ·
                      refine ⟨963583418769137137119809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569555783384365698986157 963583418769137137119809)
                      ·
                        rfl

theorem cell23_1876572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1876572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876572 prefixEnd_1876572 := by exact prefixLift 1876572
  have htrace : WordTrace (prefixWord ++ tailWord_1876572) baseStart_1876572 baseEnd_1876572 := by
    simpa [prefixWord, tailWord_1876572, baseEnd_1876572] using wordTrace_append hprefix tailTrace_1876572
  have hstable : (prefixWord ++ tailWord_1876572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876572).length < 2 ^ (prefixWord ++ tailWord_1876572).sum := by decide
  have hdescent : baseEnd_1876572 < baseStart_1876572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876601 : List Nat := [1, 2, 1, 3, 3, 3, 3, 7]
def baseStart_1876601 : Nat := 118140960795 + 1876601 * 2 ^ 59
def prefixEnd_1876601 : Nat := 4983230072969 + 3 ^ 40 * 1876601 * 2
def baseEnd_1876601 : Nat := 35688826285485834209525

theorem tailTrace_1876601 : CollatzResearch.WordTrace tailWord_1876601 prefixEnd_1876601 35688826285485834209525 := by
  unfold tailWord_1876601
  simp only [CollatzResearch.WordTrace]
  refine ⟨68445261474402549779765657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45630174316268366519843771 68445261474402549779765657)
  ·
    refine ⟨51333946105801912334824243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68445261474402549779765657 51333946105801912334824243)
    ·
      refine ⟨77000919158702868502236365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51333946105801912334824243 77000919158702868502236365)
      ·
        refine ⟨28875344684513575688338637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77000919158702868502236365 28875344684513575688338637)
        ·
          refine ⟨10828254256692590883126989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28875344684513575688338637 10828254256692590883126989)
          ·
            refine ⟨4060595346259721581172621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10828254256692590883126989 4060595346259721581172621)
            ·
              refine ⟨1522723254847395592939733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060595346259721581172621 1522723254847395592939733)
              ·
                refine ⟨35688826285485834209525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1522723254847395592939733 35688826285485834209525)
                ·
                  rfl

theorem cell23_1876601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 3, 7].length) (baseStart_1876601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876601 prefixEnd_1876601 := by exact prefixLift 1876601
  have htrace : WordTrace (prefixWord ++ tailWord_1876601) baseStart_1876601 baseEnd_1876601 := by
    simpa [prefixWord, tailWord_1876601, baseEnd_1876601] using wordTrace_append hprefix tailTrace_1876601
  have hstable : (prefixWord ++ tailWord_1876601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876601).length < 2 ^ (prefixWord ++ tailWord_1876601).sum := by decide
  have hdescent : baseEnd_1876601 < baseStart_1876601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876611 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3]
def baseStart_1876611 : Nat := 118140960795 + 1876611 * 2 ^ 59
def prefixEnd_1876611 : Nat := 4983230072969 + 3 ^ 40 * 1876611 * 2
def baseEnd_1876611 : Nat := 963603444514662484532129

theorem tailTrace_1876611 : CollatzResearch.WordTrace tailWord_1876611 prefixEnd_1876611 963603444514662484532129 := by
  unfold tailWord_1876611
  simp only [CollatzResearch.WordTrace]
  refine ⟨68445626204366321487629687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45630417469577547658419791 68445626204366321487629687)
  ·
    refine ⟨102668439306549482231444531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68445626204366321487629687 102668439306549482231444531)
    ·
      refine ⟨154002658959824223347166797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102668439306549482231444531 154002658959824223347166797)
      ·
        refine ⟨57750997109934083755187549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154002658959824223347166797 57750997109934083755187549)
        ·
          refine ⟨21656623916225281408195331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57750997109934083755187549 21656623916225281408195331)
          ·
            refine ⟨32484935874337922112292997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21656623916225281408195331 32484935874337922112292997)
            ·
              refine ⟨6090925476438360396054937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32484935874337922112292997 6090925476438360396054937)
              ·
                refine ⟨4568194107328770297041203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090925476438360396054937 4568194107328770297041203)
                ·
                  refine ⟨6852291160993155445561805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568194107328770297041203 6852291160993155445561805)
                  ·
                    refine ⟨2569609185372433292085677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6852291160993155445561805 2569609185372433292085677)
                    ·
                      refine ⟨963603444514662484532129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569609185372433292085677 963603444514662484532129)
                      ·
                        rfl

theorem cell23_1876611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_1876611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876611 prefixEnd_1876611 := by exact prefixLift 1876611
  have htrace : WordTrace (prefixWord ++ tailWord_1876611) baseStart_1876611 baseEnd_1876611 := by
    simpa [prefixWord, tailWord_1876611, baseEnd_1876611] using wordTrace_append hprefix tailTrace_1876611
  have hstable : (prefixWord ++ tailWord_1876611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876611).length < 2 ^ (prefixWord ++ tailWord_1876611).sum := by decide
  have hdescent : baseEnd_1876611 < baseStart_1876611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876612 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 1, 2, 2]
def baseStart_1876612 : Nat := 118140960795 + 1876612 * 2 ^ 59
def prefixEnd_1876612 : Nat := 4983230072969 + 3 ^ 40 * 1876612 * 2
def baseEnd_1876612 : Nat := 963603957995316980619625

theorem tailTrace_1876612 : CollatzResearch.WordTrace tailWord_1876612 prefixEnd_1876612 963603957995316980619625 := by
  unfold tailWord_1876612
  simp only [CollatzResearch.WordTrace]
  refine ⟨34222831338681349329208045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45630441784908465772277393 34222831338681349329208045)
  ·
    refine ⟨12833561752005505998453017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34222831338681349329208045 12833561752005505998453017)
    ·
      refine ⟨9625171314004129498839763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12833561752005505998453017 9625171314004129498839763)
      ·
        refine ⟨14437756971006194248259645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9625171314004129498839763 14437756971006194248259645)
        ·
          refine ⟨5414158864127322843097367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14437756971006194248259645 5414158864127322843097367)
          ·
            refine ⟨8121238296190984264646051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414158864127322843097367 8121238296190984264646051)
            ·
              refine ⟨12181857444286476396969077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121238296190984264646051 12181857444286476396969077)
              ·
                refine ⟨1142049135401857162215851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12181857444286476396969077 1142049135401857162215851)
                ·
                  refine ⟨1713073703102785743323777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142049135401857162215851 1713073703102785743323777)
                  ·
                    refine ⟨1284805277327089307492833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1713073703102785743323777 1284805277327089307492833)
                    ·
                      refine ⟨963603957995316980619625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284805277327089307492833 963603957995316980619625)
                      ·
                        rfl

theorem cell23_1876612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 2, 2].length) (baseStart_1876612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876612 prefixEnd_1876612 := by exact prefixLift 1876612
  have htrace : WordTrace (prefixWord ++ tailWord_1876612) baseStart_1876612 baseEnd_1876612 := by
    simpa [prefixWord, tailWord_1876612, baseEnd_1876612] using wordTrace_append hprefix tailTrace_1876612
  have hstable : (prefixWord ++ tailWord_1876612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876612).length < 2 ^ (prefixWord ++ tailWord_1876612).sum := by decide
  have hdescent : baseEnd_1876612 < baseStart_1876612 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876655 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 1, 3, 2]
def baseStart_1876655 : Nat := 118140960795 + 1876655 * 2 ^ 59
def prefixEnd_1876655 : Nat := 4983230072969 + 3 ^ 40 * 1876655 * 2
def baseEnd_1876655 : Nat := 963626037663460312381927

theorem tailTrace_1876655 : CollatzResearch.WordTrace tailWord_1876655 prefixEnd_1876655 963626037663460312381927 := by
  unfold tailWord_1876655
  simp only [CollatzResearch.WordTrace]
  refine ⟨68447231016206917002231419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45631487344137944668154279 68447231016206917002231419)
  ·
    refine ⟨102670846524310375503347129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68447231016206917002231419 102670846524310375503347129)
    ·
      refine ⟨77003134893232781627510347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102670846524310375503347129 77003134893232781627510347)
      ·
        refine ⟨115504702339849172441265521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77003134893232781627510347 115504702339849172441265521)
        ·
          refine ⟨86628526754886879330949141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115504702339849172441265521 86628526754886879330949141)
          ·
            refine ⟨4060712191635322468638241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86628526754886879330949141 4060712191635322468638241)
            ·
              refine ⟨3045534143726491851478681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4060712191635322468638241 3045534143726491851478681)
              ·
                refine ⟨2284150607794868888609011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3045534143726491851478681 2284150607794868888609011)
                ·
                  refine ⟨3426225911692303332913517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284150607794868888609011 3426225911692303332913517)
                  ·
                    refine ⟨1284834716884613749842569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426225911692303332913517 1284834716884613749842569)
                    ·
                      refine ⟨963626037663460312381927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284834716884613749842569 963626037663460312381927)
                      ·
                        rfl

theorem cell23_1876655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 3, 2].length) (baseStart_1876655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876655 prefixEnd_1876655 := by exact prefixLift 1876655
  have htrace : WordTrace (prefixWord ++ tailWord_1876655) baseStart_1876655 baseEnd_1876655 := by
    simpa [prefixWord, tailWord_1876655, baseEnd_1876655] using wordTrace_append hprefix tailTrace_1876655
  have hstable : (prefixWord ++ tailWord_1876655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876655).length < 2 ^ (prefixWord ++ tailWord_1876655).sum := by decide
  have hdescent : baseEnd_1876655 < baseStart_1876655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876668 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_1876668 : Nat := 118140960795 + 1876668 * 2 ^ 59
def prefixEnd_1876668 : Nat := 4983230072969 + 3 ^ 40 * 1876668 * 2
def baseEnd_1876668 : Nat := 963632712911968761519367

theorem tailTrace_1876668 : CollatzResearch.WordTrace tailWord_1876668 prefixEnd_1876668 963632712911968761519367 := by
  unfold tailWord_1876668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34223852582579910111227329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45631803443439880148303105 34223852582579910111227329)
  ·
    refine ⟨25667889436934932583420497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34223852582579910111227329 25667889436934932583420497)
    ·
      refine ⟨19250917077701199437565373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25667889436934932583420497 19250917077701199437565373)
      ·
        refine ⟨7219093904137949789087015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19250917077701199437565373 7219093904137949789087015)
        ·
          refine ⟨10828640856206924683630523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219093904137949789087015 10828640856206924683630523)
          ·
            refine ⟨16242961284310387025445785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828640856206924683630523 16242961284310387025445785)
            ·
              refine ⟨12182220963232790269084339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16242961284310387025445785 12182220963232790269084339)
              ·
                refine ⟨18273331444849185403626509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12182220963232790269084339 18273331444849185403626509)
                ·
                  refine ⟨6852499291818444526359941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18273331444849185403626509 6852499291818444526359941)
                  ·
                    refine ⟨1284843617215958348692489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6852499291818444526359941 1284843617215958348692489)
                    ·
                      refine ⟨963632712911968761519367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284843617215958348692489 963632712911968761519367)
                      ·
                        rfl

theorem cell23_1876668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_1876668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876668 prefixEnd_1876668 := by exact prefixLift 1876668
  have htrace : WordTrace (prefixWord ++ tailWord_1876668) baseStart_1876668 baseEnd_1876668 := by
    simpa [prefixWord, tailWord_1876668, baseEnd_1876668] using wordTrace_append hprefix tailTrace_1876668
  have hstable : (prefixWord ++ tailWord_1876668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876668).length < 2 ^ (prefixWord ++ tailWord_1876668).sum := by decide
  have hdescent : baseEnd_1876668 < baseStart_1876668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876671 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5]
def baseStart_1876671 : Nat := 118140960795 + 1876671 * 2 ^ 59
def prefixEnd_1876671 : Nat := 4983230072969 + 3 ^ 40 * 1876671 * 2
def baseEnd_1876671 : Nat := 963634253353932249781853

theorem tailTrace_1876671 : CollatzResearch.WordTrace tailWord_1876671 prefixEnd_1876671 963634253353932249781853 := by
  unfold tailWord_1876671
  simp only [CollatzResearch.WordTrace]
  refine ⟨68447814584148951734813867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45631876389432634489875911 68447814584148951734813867)
  ·
    refine ⟨102671721876223427602220801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68447814584148951734813867 102671721876223427602220801)
    ·
      refine ⟨77003791407167570701665601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102671721876223427602220801 77003791407167570701665601)
      ·
        refine ⟨57752843555375678026249201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77003791407167570701665601 57752843555375678026249201)
        ·
          refine ⟨43314632666531758519686901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57752843555375678026249201 43314632666531758519686901)
          ·
            refine ⟨4060746812487352361220647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43314632666531758519686901 4060746812487352361220647)
            ·
              refine ⟨6091120218731028541830971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060746812487352361220647 6091120218731028541830971)
              ·
                refine ⟨9136680328096542812746457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091120218731028541830971 9136680328096542812746457)
                ·
                  refine ⟨6852510246072407109559843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9136680328096542812746457 6852510246072407109559843)
                  ·
                    refine ⟨10278765369108610664339765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6852510246072407109559843 10278765369108610664339765)
                    ·
                      refine ⟨963634253353932249781853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10278765369108610664339765 963634253353932249781853)
                      ·
                        rfl

theorem cell23_1876671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_1876671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876671 prefixEnd_1876671 := by exact prefixLift 1876671
  have htrace : WordTrace (prefixWord ++ tailWord_1876671) baseStart_1876671 baseEnd_1876671 := by
    simpa [prefixWord, tailWord_1876671, baseEnd_1876671] using wordTrace_append hprefix tailTrace_1876671
  have hstable : (prefixWord ++ tailWord_1876671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876671).length < 2 ^ (prefixWord ++ tailWord_1876671).sum := by decide
  have hdescent : baseEnd_1876671 < baseStart_1876671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876768 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 5, 4]
def baseStart_1876768 : Nat := 118140960795 + 1876768 * 2 ^ 59
def prefixEnd_1876768 : Nat := 4983230072969 + 3 ^ 40 * 1876768 * 2
def baseEnd_1876768 : Nat := 321228020325806123422969

theorem tailTrace_1876768 : CollatzResearch.WordTrace tailWord_1876768 prefixEnd_1876768 321228020325806123422969 := by
  unfold tailWord_1876768
  simp only [CollatzResearch.WordTrace]
  refine ⟨34225676232398768650547479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45634234976531691534063305 34225676232398768650547479)
  ·
    refine ⟨51338514348598152975821219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34225676232398768650547479 51338514348598152975821219)
    ·
      refine ⟨77007771522897229463731829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51338514348598152975821219 77007771522897229463731829)
      ·
        refine ⟨7219478580271615262224859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77007771522897229463731829 7219478580271615262224859)
        ·
          refine ⟨10829217870407422893337289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219478580271615262224859 10829217870407422893337289)
          ·
            refine ⟨8121913402805567170002967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10829217870407422893337289 8121913402805567170002967)
            ·
              refine ⟨12182870104208350755004451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8121913402805567170002967 12182870104208350755004451)
              ·
                refine ⟨18274305156312526132506677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12182870104208350755004451 18274305156312526132506677)
                ·
                  refine ⟨1713216108404299324922501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18274305156312526132506677 1713216108404299324922501)
                  ·
                    refine ⟨321228020325806123422969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713216108404299324922501 321228020325806123422969)
                    ·
                      rfl

theorem cell23_1876768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 5, 4].length) (baseStart_1876768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876768 prefixEnd_1876768 := by exact prefixLift 1876768
  have htrace : WordTrace (prefixWord ++ tailWord_1876768) baseStart_1876768 baseEnd_1876768 := by
    simpa [prefixWord, tailWord_1876768, baseEnd_1876768] using wordTrace_append hprefix tailTrace_1876768
  have hstable : (prefixWord ++ tailWord_1876768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876768).length < 2 ^ (prefixWord ++ tailWord_1876768).sum := by decide
  have hdescent : baseEnd_1876768 < baseStart_1876768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876772 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 2, 5]
def baseStart_1876772 : Nat := 118140960795 + 1876772 * 2 ^ 59
def prefixEnd_1876772 : Nat := 4983230072969 + 3 ^ 40 * 1876772 * 2
def baseEnd_1876772 : Nat := 321228704966678784872963

theorem tailTrace_1876772 : CollatzResearch.WordTrace tailWord_1876772 prefixEnd_1876772 321228704966678784872963 := by
  unfold tailWord_1876772
  simp only [CollatzResearch.WordTrace]
  refine ⟨34225749178391522992120285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45634332237855363989493713 34225749178391522992120285)
  ·
    refine ⟨12834655941896821122045107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34225749178391522992120285 12834655941896821122045107)
    ·
      refine ⟨19251983912845231683067661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12834655941896821122045107 19251983912845231683067661)
      ·
        refine ⟨7219493967316961881150373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19251983912845231683067661 7219493967316961881150373)
        ·
          refine ⟨1353655118871930352715695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7219493967316961881150373 1353655118871930352715695)
          ·
            refine ⟨2030482678307895529073543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353655118871930352715695 2030482678307895529073543)
            ·
              refine ⟨3045724017461843293610315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030482678307895529073543 3045724017461843293610315)
              ·
                refine ⟨4568586026192764940415473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3045724017461843293610315 4568586026192764940415473)
                ·
                  refine ⟨3426439519644573705311605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4568586026192764940415473 3426439519644573705311605)
                  ·
                    refine ⟨321228704966678784872963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3426439519644573705311605 321228704966678784872963)
                    ·
                      rfl

theorem cell23_1876772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 2, 5].length) (baseStart_1876772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876772 prefixEnd_1876772 := by exact prefixLift 1876772
  have htrace : WordTrace (prefixWord ++ tailWord_1876772) baseStart_1876772 baseEnd_1876772 := by
    simpa [prefixWord, tailWord_1876772, baseEnd_1876772] using wordTrace_append hprefix tailTrace_1876772
  have hstable : (prefixWord ++ tailWord_1876772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876772).length < 2 ^ (prefixWord ++ tailWord_1876772).sum := by decide
  have hdescent : baseEnd_1876772 < baseStart_1876772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876825 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 3]
def baseStart_1876825 : Nat := 118140960795 + 1876825 * 2 ^ 59
def prefixEnd_1876825 : Nat := 4983230072969 + 3 ^ 40 * 1876825 * 2
def baseEnd_1876825 : Nat := 963713329374724647256145

theorem tailTrace_1876825 : CollatzResearch.WordTrace tailWord_1876825 prefixEnd_1876825 963713329374724647256145 := by
  unfold tailWord_1876825
  simp only [CollatzResearch.WordTrace]
  refine ⟨68453431425591036035919929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45635620950394024023946619 68453431425591036035919929)
  ·
    refine ⟨51340073569193277026939947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68453431425591036035919929 51340073569193277026939947)
    ·
      refine ⟨77010110353789915540409921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51340073569193277026939947 77010110353789915540409921)
      ·
        refine ⟨57757582765342436655307441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77010110353789915540409921 57757582765342436655307441)
        ·
          refine ⟨43318187074006827491480581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57757582765342436655307441 43318187074006827491480581)
          ·
            refine ⟨8122160076376280154652609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43318187074006827491480581 8122160076376280154652609)
            ·
              refine ⟨6091620057282210115989457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122160076376280154652609 6091620057282210115989457)
              ·
                refine ⟨4568715042961657586992093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091620057282210115989457 4568715042961657586992093)
                ·
                  refine ⟨1713268141110621595122035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4568715042961657586992093 1713268141110621595122035)
                  ·
                    refine ⟨2569902211665932392683053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713268141110621595122035 2569902211665932392683053)
                    ·
                      refine ⟨963713329374724647256145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569902211665932392683053 963713329374724647256145)
                      ·
                        rfl

theorem cell23_1876825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 3, 1, 3].length) (baseStart_1876825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876825 prefixEnd_1876825 := by exact prefixLift 1876825
  have htrace : WordTrace (prefixWord ++ tailWord_1876825) baseStart_1876825 baseEnd_1876825 := by
    simpa [prefixWord, tailWord_1876825, baseEnd_1876825] using wordTrace_append hprefix tailTrace_1876825
  have hstable : (prefixWord ++ tailWord_1876825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876825).length < 2 ^ (prefixWord ++ tailWord_1876825).sum := by decide
  have hdescent : baseEnd_1876825 < baseStart_1876825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876835 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 5, 2]
def baseStart_1876835 : Nat := 118140960795 + 1876835 * 2 ^ 59
def prefixEnd_1876835 : Nat := 4983230072969 + 3 ^ 40 * 1876835 * 2
def baseEnd_1876835 : Nat := 963718464181269608131099

theorem tailTrace_1876835 : CollatzResearch.WordTrace tailWord_1876835 prefixEnd_1876835 963718464181269608131099 := by
  unfold tailWord_1876835
  simp only [CollatzResearch.WordTrace]
  refine ⟨68453796155554807743783959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45635864103703205162522639 68453796155554807743783959)
  ·
    refine ⟨102680694233332211615675939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68453796155554807743783959 102680694233332211615675939)
    ·
      refine ⟨154021041349998317423513909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102680694233332211615675939 154021041349998317423513909)
      ·
        refine ⟨14439472626562342258454429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154021041349998317423513909 14439472626562342258454429)
        ·
          refine ⟨5414802234960878346920411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14439472626562342258454429 5414802234960878346920411)
          ·
            refine ⟨8122203352441317520380617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414802234960878346920411 8122203352441317520380617)
            ·
              refine ⟨6091652514330988140285463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122203352441317520380617 6091652514330988140285463)
              ·
                refine ⟨9137478771496482210428195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091652514330988140285463 9137478771496482210428195)
                ·
                  refine ⟨13706218157244723315642293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9137478771496482210428195 13706218157244723315642293)
                  ·
                    refine ⟨1284957952241692810841465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13706218157244723315642293 1284957952241692810841465)
                    ·
                      refine ⟨963718464181269608131099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284957952241692810841465 963718464181269608131099)
                      ·
                        rfl

theorem cell23_1876835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_1876835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876835 prefixEnd_1876835 := by exact prefixLift 1876835
  have htrace : WordTrace (prefixWord ++ tailWord_1876835) baseStart_1876835 baseEnd_1876835 := by
    simpa [prefixWord, tailWord_1876835, baseEnd_1876835] using wordTrace_append hprefix tailTrace_1876835
  have hstable : (prefixWord ++ tailWord_1876835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876835).length < 2 ^ (prefixWord ++ tailWord_1876835).sum := by decide
  have hdescent : baseEnd_1876835 < baseStart_1876835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876866 : List Nat := [3, 4, 2, 2, 1, 2, 2, 1, 6]
def baseStart_1876866 : Nat := 118140960795 + 1876866 * 2 ^ 59
def prefixEnd_1876866 : Nat := 4983230072969 + 3 ^ 40 * 1876866 * 2
def baseEnd_1876866 : Nat := 107081598009062109649273

theorem tailTrace_1876866 : CollatzResearch.WordTrace tailWord_1876866 prefixEnd_1876866 107081598009062109649273 := by
  unfold tailWord_1876866
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113731704610625009540613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45636617878961666692108301 17113731704610625009540613)
  ·
    refine ⟨3208824694614492189288865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17113731704610625009540613 3208824694614492189288865)
    ·
      refine ⟨2406618520960869141966649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208824694614492189288865 2406618520960869141966649)
      ·
        refine ⟨1804963890720651856474987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2406618520960869141966649 1804963890720651856474987)
        ·
          refine ⟨2707445836080977784712481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804963890720651856474987 2707445836080977784712481)
          ·
            refine ⟨2030584377060733338534361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707445836080977784712481 2030584377060733338534361)
            ·
              refine ⟨1522938282795550003900771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030584377060733338534361 1522938282795550003900771)
              ·
                refine ⟨2284407424193325005851157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522938282795550003900771 2284407424193325005851157)
                ·
                  refine ⟨107081598009062109649273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2284407424193325005851157 107081598009062109649273)
                  ·
                    rfl

theorem cell23_1876866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_1876866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876866 prefixEnd_1876866 := by exact prefixLift 1876866
  have htrace : WordTrace (prefixWord ++ tailWord_1876866) baseStart_1876866 baseEnd_1876866 := by
    simpa [prefixWord, tailWord_1876866, baseEnd_1876866] using wordTrace_append hprefix tailTrace_1876866
  have hstable : (prefixWord ++ tailWord_1876866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876866).length < 2 ^ (prefixWord ++ tailWord_1876866).sum := by decide
  have hdescent : baseEnd_1876866 < baseStart_1876866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876868 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_1876868 : Nat := 118140960795 + 1876868 * 2 ^ 59
def prefixEnd_1876868 : Nat := 4983230072969 + 3 ^ 40 * 1876868 * 2
def baseEnd_1876868 : Nat := 963735409042867979018447

theorem tailTrace_1876868 : CollatzResearch.WordTrace tailWord_1876868 prefixEnd_1876868 963735409042867979018447 := by
  unfold tailWord_1876868
  simp only [CollatzResearch.WordTrace]
  refine ⟨34227499882217627189867629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45636666509623502919823505 34227499882217627189867629)
  ·
    refine ⟨12835312455831610196200361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34227499882217627189867629 12835312455831610196200361)
    ·
      refine ⟨9626484341873707647150271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12835312455831610196200361 9626484341873707647150271)
      ·
        refine ⟨14439726512810561470725407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626484341873707647150271 14439726512810561470725407)
        ·
          refine ⟨21659589769215842206088111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14439726512810561470725407 21659589769215842206088111)
          ·
            refine ⟨32489384653823763309132167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21659589769215842206088111 32489384653823763309132167)
            ·
              refine ⟨48734076980735644963698251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32489384653823763309132167 48734076980735644963698251)
              ·
                refine ⟨73101115471103467445547377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48734076980735644963698251 73101115471103467445547377)
                ·
                  refine ⟨54825836603327600584160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73101115471103467445547377 54825836603327600584160533)
                  ·
                    refine ⟨2569961090780981277382525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 54825836603327600584160533 2569961090780981277382525)
                    ·
                      refine ⟨963735409042867979018447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569961090780981277382525 963735409042867979018447)
                      ·
                        rfl

theorem cell23_1876868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_1876868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876868 prefixEnd_1876868 := by exact prefixLift 1876868
  have htrace : WordTrace (prefixWord ++ tailWord_1876868) baseStart_1876868 baseEnd_1876868 := by
    simpa [prefixWord, tailWord_1876868, baseEnd_1876868] using wordTrace_append hprefix tailTrace_1876868
  have hstable : (prefixWord ++ tailWord_1876868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876868).length < 2 ^ (prefixWord ++ tailWord_1876868).sum := by decide
  have hdescent : baseEnd_1876868 < baseStart_1876868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876882 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_1876882 : Nat := 118140960795 + 1876882 * 2 ^ 59
def prefixEnd_1876882 : Nat := 4983230072969 + 3 ^ 40 * 1876882 * 2
def baseEnd_1876882 : Nat := 963742597772030924243383

theorem tailTrace_1876882 : CollatzResearch.WordTrace tailWord_1876882 prefixEnd_1876882 963742597772030924243383 := by
  unfold tailWord_1876882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113877596596133692686225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45637006924256356513829933 17113877596596133692686225)
  ·
    refine ⟨12835408197447100269514669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17113877596596133692686225 12835408197447100269514669)
    ·
      refine ⟨4813278074042662601068001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12835408197447100269514669 4813278074042662601068001)
      ·
        refine ⟨3609958555531996950801001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4813278074042662601068001 3609958555531996950801001)
        ·
          refine ⟨2707468916648997713100751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3609958555531996950801001 2707468916648997713100751)
          ·
            refine ⟨4061203374973496569651127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707468916648997713100751 4061203374973496569651127)
            ·
              refine ⟨6091805062460244854476691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061203374973496569651127 6091805062460244854476691)
              ·
                refine ⟨9137707593690367281715037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091805062460244854476691 9137707593690367281715037)
                ·
                  refine ⟨3426640347633887730643139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9137707593690367281715037 3426640347633887730643139)
                  ·
                    refine ⟨5139960521450831595964709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426640347633887730643139 5139960521450831595964709)
                    ·
                      refine ⟨963742597772030924243383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5139960521450831595964709 963742597772030924243383)
                      ·
                        rfl

theorem cell23_1876882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_1876882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876882 prefixEnd_1876882 := by exact prefixLift 1876882
  have htrace : WordTrace (prefixWord ++ tailWord_1876882) baseStart_1876882 baseEnd_1876882 := by
    simpa [prefixWord, tailWord_1876882, baseEnd_1876882] using wordTrace_append hprefix tailTrace_1876882
  have hstable : (prefixWord ++ tailWord_1876882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876882).length < 2 ^ (prefixWord ++ tailWord_1876882).sum := by decide
  have hdescent : baseEnd_1876882 < baseStart_1876882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876885 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_1876885 : Nat := 118140960795 + 1876885 * 2 ^ 59
def prefixEnd_1876885 : Nat := 4983230072969 + 3 ^ 40 * 1876885 * 2
def baseEnd_1876885 : Nat := 963744138213994412505869

theorem tailTrace_1876885 : CollatzResearch.WordTrace tailWord_1876885 prefixEnd_1876885 963744138213994412505869 := by
  unfold tailWord_1876885
  simp only [CollatzResearch.WordTrace]
  refine ⟨68455619805373666283104109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45637079870249110855402739 68455619805373666283104109)
  ·
    refine ⟨25670857427015124856164041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68455619805373666283104109 25670857427015124856164041)
    ·
      refine ⟨19253143070261343642123031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25670857427015124856164041 19253143070261343642123031)
      ·
        refine ⟨28879714605392015463184547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19253143070261343642123031 28879714605392015463184547)
        ·
          refine ⟨43319571908088023194776821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28879714605392015463184547 43319571908088023194776821)
          ·
            refine ⟨4061209866383252174510327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43319571908088023194776821 4061209866383252174510327)
            ·
              refine ⟨6091814799574878261765491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061209866383252174510327 6091814799574878261765491)
              ·
                refine ⟨9137722199362317392648237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091814799574878261765491 9137722199362317392648237)
                ·
                  refine ⟨3426645824760869022243089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9137722199362317392648237 3426645824760869022243089)
                  ·
                    refine ⟨2569984368570651766682317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3426645824760869022243089 2569984368570651766682317)
                    ·
                      refine ⟨963744138213994412505869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2569984368570651766682317 963744138213994412505869)
                      ·
                        rfl

theorem cell23_1876885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_1876885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876885 prefixEnd_1876885 := by exact prefixLift 1876885
  have htrace : WordTrace (prefixWord ++ tailWord_1876885) baseStart_1876885 baseEnd_1876885 := by
    simpa [prefixWord, tailWord_1876885, baseEnd_1876885] using wordTrace_append hprefix tailTrace_1876885
  have hstable : (prefixWord ++ tailWord_1876885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876885).length < 2 ^ (prefixWord ++ tailWord_1876885).sum := by decide
  have hdescent : baseEnd_1876885 < baseStart_1876885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876886 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1876886 : Nat := 118140960795 + 1876886 * 2 ^ 59
def prefixEnd_1876886 : Nat := 4983230072969 + 3 ^ 40 * 1876886 * 2
def baseEnd_1876886 : Nat := 963744651694648908593365

theorem tailTrace_1876886 : CollatzResearch.WordTrace tailWord_1876886 prefixEnd_1876886 963744651694648908593365 := by
  unfold tailWord_1876886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278478517398127715868157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45637104185580028969260341 4278478517398127715868157)
  ·
    refine ⟨1604429444024297893450559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4278478517398127715868157 1604429444024297893450559)
    ·
      refine ⟨2406644166036446840175839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604429444024297893450559 2406644166036446840175839)
      ·
        refine ⟨3609966249054670260263759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406644166036446840175839 3609966249054670260263759)
        ·
          refine ⟨5414949373582005390395639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609966249054670260263759 5414949373582005390395639)
          ·
            refine ⟨8122424060373008085593459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414949373582005390395639 8122424060373008085593459)
            ·
              refine ⟨12183636090559512128390189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8122424060373008085593459 12183636090559512128390189)
              ·
                refine ⟨4568863533959817048146321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12183636090559512128390189 4568863533959817048146321)
                ·
                  refine ⟨3426647650469862786109741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4568863533959817048146321 3426647650469862786109741)
                  ·
                    refine ⟨1284992868926198544791153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426647650469862786109741 1284992868926198544791153)
                    ·
                      refine ⟨963744651694648908593365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1284992868926198544791153 963744651694648908593365)
                      ·
                        rfl

theorem cell23_1876886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1876886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876886 prefixEnd_1876886 := by exact prefixLift 1876886
  have htrace : WordTrace (prefixWord ++ tailWord_1876886) baseStart_1876886 baseEnd_1876886 := by
    simpa [prefixWord, tailWord_1876886, baseEnd_1876886] using wordTrace_append hprefix tailTrace_1876886
  have hstable : (prefixWord ++ tailWord_1876886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876886).length < 2 ^ (prefixWord ++ tailWord_1876886).sum := by decide
  have hdescent : baseEnd_1876886 < baseStart_1876886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876895 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1876895 : Nat := 118140960795 + 1876895 * 2 ^ 59
def prefixEnd_1876895 : Nat := 4983230072969 + 3 ^ 40 * 1876895 * 2
def baseEnd_1876895 : Nat := 963749273020539373380823

theorem tailTrace_1876895 : CollatzResearch.WordTrace tailWord_1876895 prefixEnd_1876895 963749273020539373380823 := by
  unfold tailWord_1876895
  simp only [CollatzResearch.WordTrace]
  refine ⟨68455984535337437990968139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45637323023558291993978759 68455984535337437990968139)
  ·
    refine ⟨102683976803006156986452209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68455984535337437990968139 102683976803006156986452209)
    ·
      refine ⟨77012982602254617739839157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102683976803006156986452209 77012982602254617739839157)
      ·
        refine ⟨7219967118961370413109921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77012982602254617739839157 7219967118961370413109921)
        ·
          refine ⟨5414975339221027809832441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7219967118961370413109921 5414975339221027809832441)
          ·
            refine ⟨4061231504415770857374331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5414975339221027809832441 4061231504415770857374331)
            ·
              refine ⟨6091847256623656286061497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061231504415770857374331 6091847256623656286061497)
              ·
                refine ⟨4568885442467742214546123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6091847256623656286061497 4568885442467742214546123)
                ·
                  refine ⟨6853328163701613321819185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4568885442467742214546123 6853328163701613321819185)
                  ·
                    refine ⟨5139996122776209991364389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6853328163701613321819185 5139996122776209991364389)
                    ·
                      refine ⟨963749273020539373380823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5139996122776209991364389 963749273020539373380823)
                      ·
                        rfl

theorem cell23_1876895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1876895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876895 prefixEnd_1876895 := by exact prefixLift 1876895
  have htrace : WordTrace (prefixWord ++ tailWord_1876895) baseStart_1876895 baseEnd_1876895 := by
    simpa [prefixWord, tailWord_1876895, baseEnd_1876895] using wordTrace_append hprefix tailTrace_1876895
  have hstable : (prefixWord ++ tailWord_1876895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876895).length < 2 ^ (prefixWord ++ tailWord_1876895).sum := by decide
  have hdescent : baseEnd_1876895 < baseStart_1876895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876938 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_1876938 : Nat := 118140960795 + 1876938 * 2 ^ 59
def prefixEnd_1876938 : Nat := 4983230072969 + 3 ^ 40 * 1876938 * 2
def baseEnd_1876938 : Nat := 963771352688682705143125

theorem tailTrace_1876938 : CollatzResearch.WordTrace tailWord_1876938 prefixEnd_1876938 963771352688682705143125 := by
  unfold tailWord_1876938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17114388218545414083695867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45638368582787770889855645 17114388218545414083695867)
  ·
    refine ⟨25671582327818121125543801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17114388218545414083695867 25671582327818121125543801)
    ·
      refine ⟨19253686745863590844157851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25671582327818121125543801 19253686745863590844157851)
      ·
        refine ⟨28880530118795386266236777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19253686745863590844157851 28880530118795386266236777)
        ·
          refine ⟨21660397589096539699677583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28880530118795386266236777 21660397589096539699677583)
          ·
            refine ⟨32490596383644809549516375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21660397589096539699677583 32490596383644809549516375)
            ·
              refine ⟨48735894575467214324274563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32490596383644809549516375 48735894575467214324274563)
              ·
                refine ⟨73103841863200821486411845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48735894575467214324274563 73103841863200821486411845)
                ·
                  refine ⟨13706970349350154028702221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73103841863200821486411845 13706970349350154028702221)
                  ·
                    refine ⟨5140113881006307760763333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13706970349350154028702221 5140113881006307760763333)
                    ·
                      refine ⟨963771352688682705143125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5140113881006307760763333 963771352688682705143125)
                      ·
                        rfl

theorem cell23_1876938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_1876938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876938 prefixEnd_1876938 := by exact prefixLift 1876938
  have htrace : WordTrace (prefixWord ++ tailWord_1876938) baseStart_1876938 baseEnd_1876938 := by
    simpa [prefixWord, tailWord_1876938, baseEnd_1876938] using wordTrace_append hprefix tailTrace_1876938
  have hstable : (prefixWord ++ tailWord_1876938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876938).length < 2 ^ (prefixWord ++ tailWord_1876938).sum := by decide
  have hdescent : baseEnd_1876938 < baseStart_1876938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876942 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2]
def baseStart_1876942 : Nat := 118140960795 + 1876942 * 2 ^ 59
def prefixEnd_1876942 : Nat := 4983230072969 + 3 ^ 40 * 1876942 * 2
def baseEnd_1876942 : Nat := 963773406611300689493107

theorem tailTrace_1876942 : CollatzResearch.WordTrace tailWord_1876942 prefixEnd_1876942 963773406611300689493107 := by
  unfold tailWord_1876942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557212345770895627241135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45638465844111443345286053 8557212345770895627241135)
  ·
    refine ⟨12835818518656343440861703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8557212345770895627241135 12835818518656343440861703)
    ·
      refine ⟨19253727777984515161292555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12835818518656343440861703 19253727777984515161292555)
      ·
        refine ⟨28880591666976772741938833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19253727777984515161292555 28880591666976772741938833)
        ·
          refine ⟨21660443750232579556454125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28880591666976772741938833 21660443750232579556454125)
          ·
            refine ⟨8122666406337217333670297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21660443750232579556454125 8122666406337217333670297)
            ·
              refine ⟨6091999804752913000252723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8122666406337217333670297 6091999804752913000252723)
              ·
                refine ⟨9137999707129369500379085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091999804752913000252723 9137999707129369500379085)
                ·
                  refine ⟨3426749890173513562642157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9137999707129369500379085 3426749890173513562642157)
                  ·
                    refine ⟨1285031208815067585990809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426749890173513562642157 1285031208815067585990809)
                    ·
                      refine ⟨963773406611300689493107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285031208815067585990809 963773406611300689493107)
                      ·
                        rfl

theorem cell23_1876942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_1876942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876942 prefixEnd_1876942 := by exact prefixLift 1876942
  have htrace : WordTrace (prefixWord ++ tailWord_1876942) baseStart_1876942 baseEnd_1876942 := by
    simpa [prefixWord, tailWord_1876942, baseEnd_1876942] using wordTrace_append hprefix tailTrace_1876942
  have hstable : (prefixWord ++ tailWord_1876942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876942).length < 2 ^ (prefixWord ++ tailWord_1876942).sum := by decide
  have hdescent : baseEnd_1876942 < baseStart_1876942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876959 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 1, 3, 2]
def baseStart_1876959 : Nat := 118140960795 + 1876959 * 2 ^ 59
def prefixEnd_1876959 : Nat := 4983230072969 + 3 ^ 40 * 1876959 * 2
def baseEnd_1876959 : Nat := 963782135782427122980529

theorem tailTrace_1876959 : CollatzResearch.WordTrace tailWord_1876959 prefixEnd_1876959 963782135782427122980529 := by
  unfold tailWord_1876959
  simp only [CollatzResearch.WordTrace]
  refine ⟨68458318807105576921297931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45638879204737051280865287 68458318807105576921297931)
  ·
    refine ⟨102687478210658365381946897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68458318807105576921297931 102687478210658365381946897)
    ·
      refine ⟨77015608657993774036460173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102687478210658365381946897 77015608657993774036460173)
      ·
        refine ⟨28880853246747665263672565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77015608657993774036460173 28880853246747665263672565)
        ·
          refine ⟨2707579991882593618469303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28880853246747665263672565 2707579991882593618469303)
          ·
            refine ⟨4061369987823890427703955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707579991882593618469303 4061369987823890427703955)
            ·
              refine ⟨6092054981735835641555933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061369987823890427703955 6092054981735835641555933)
              ·
                refine ⟨2284520618150938365583475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6092054981735835641555933 2284520618150938365583475)
                ·
                  refine ⟨3426780927226407548375213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284520618150938365583475 3426780927226407548375213)
                  ·
                    refine ⟨1285042847709902830640705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3426780927226407548375213 1285042847709902830640705)
                    ·
                      refine ⟨963782135782427122980529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285042847709902830640705 963782135782427122980529)
                      ·
                        rfl

theorem cell23_1876959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_1876959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876959 prefixEnd_1876959 := by exact prefixLift 1876959
  have htrace : WordTrace (prefixWord ++ tailWord_1876959) baseStart_1876959 baseEnd_1876959 := by
    simpa [prefixWord, tailWord_1876959, baseEnd_1876959] using wordTrace_append hprefix tailTrace_1876959
  have hstable : (prefixWord ++ tailWord_1876959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876959).length < 2 ^ (prefixWord ++ tailWord_1876959).sum := by decide
  have hdescent : baseEnd_1876959 < baseStart_1876959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876980 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1876980 : Nat := 118140960795 + 1876980 * 2 ^ 59
def prefixEnd_1876980 : Nat := 4983230072969 + 3 ^ 40 * 1876980 * 2
def baseEnd_1876980 : Nat := 963792918876171540817933

theorem tailTrace_1876980 : CollatzResearch.WordTrace tailWord_1876980 prefixEnd_1876980 963792918876171540817933 := by
  unfold tailWord_1876980
  simp only [CollatzResearch.WordTrace]
  refine ⟨34229542370014748753906197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45639389826686331671874929 34229542370014748753906197)
  ·
    refine ⟨1604509798594441347839353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34229542370014748753906197 1604509798594441347839353)
    ·
      refine ⟨1203382348945831010879515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1604509798594441347839353 1203382348945831010879515)
      ·
        refine ⟨1805073523418746516319273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203382348945831010879515 1805073523418746516319273)
        ·
          refine ⟨1353805142564059887239455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805073523418746516319273 1353805142564059887239455)
          ·
            refine ⟨2030707713846089830859183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353805142564059887239455 2030707713846089830859183)
            ·
              refine ⟨3046061570769134746288775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030707713846089830859183 3046061570769134746288775)
              ·
                refine ⟨4569092356153702119433163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046061570769134746288775 4569092356153702119433163)
                ·
                  refine ⟨6853638534230553179149745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569092356153702119433163 6853638534230553179149745)
                  ·
                    refine ⟨5140228900672914884362309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6853638534230553179149745 5140228900672914884362309)
                    ·
                      refine ⟨963792918876171540817933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5140228900672914884362309 963792918876171540817933)
                      ·
                        rfl

theorem cell23_1876980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1876980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1876980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1876980 prefixEnd_1876980 := by exact prefixLift 1876980
  have htrace : WordTrace (prefixWord ++ tailWord_1876980) baseStart_1876980 baseEnd_1876980 := by
    simpa [prefixWord, tailWord_1876980, baseEnd_1876980] using wordTrace_append hprefix tailTrace_1876980
  have hstable : (prefixWord ++ tailWord_1876980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876980).length < 2 ^ (prefixWord ++ tailWord_1876980).sum := by decide
  have hdescent : baseEnd_1876980 < baseStart_1876980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877025 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1877025 : Nat := 118140960795 + 1877025 * 2 ^ 59
def prefixEnd_1877025 : Nat := 4983230072969 + 3 ^ 40 * 1877025 * 2
def baseEnd_1877025 : Nat := 321272008501874621585075

theorem tailTrace_1877025 : CollatzResearch.WordTrace tailWord_1877025 prefixEnd_1877025 321272008501874621585075 := by
  unfold tailWord_1877025
  simp only [CollatzResearch.WordTrace]
  refine ⟨68460726024866470193200529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45640484016577646795467019 68460726024866470193200529)
  ·
    refine ⟨51345544518649852644900397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68460726024866470193200529 51345544518649852644900397)
    ·
      refine ⟨19254579194493694741837649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51345544518649852644900397 19254579194493694741837649)
      ·
        refine ⟨14440934395870271056378237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19254579194493694741837649 14440934395870271056378237)
        ·
          refine ⟨5415350398451351646141839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14440934395870271056378237 5415350398451351646141839)
          ·
            refine ⟨8123025597677027469212759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415350398451351646141839 8123025597677027469212759)
            ·
              refine ⟨12184538396515541203819139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123025597677027469212759 12184538396515541203819139)
              ·
                refine ⟨18276807594773311805728709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12184538396515541203819139 18276807594773311805728709)
                ·
                  refine ⟨3426901424019995963574133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18276807594773311805728709 3426901424019995963574133)
                  ·
                    refine ⟨321272008501874621585075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3426901424019995963574133 321272008501874621585075)
                    ·
                      rfl

theorem cell23_1877025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1877025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877025 prefixEnd_1877025 := by exact prefixLift 1877025
  have htrace : WordTrace (prefixWord ++ tailWord_1877025) baseStart_1877025 baseEnd_1877025 := by
    simpa [prefixWord, tailWord_1877025, baseEnd_1877025] using wordTrace_append hprefix tailTrace_1877025
  have hstable : (prefixWord ++ tailWord_1877025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877025).length < 2 ^ (prefixWord ++ tailWord_1877025).sum := by decide
  have hdescent : baseEnd_1877025 < baseStart_1877025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877045 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1877045 : Nat := 118140960795 + 1877045 * 2 ^ 59
def prefixEnd_1877045 : Nat := 4983230072969 + 3 ^ 40 * 1877045 * 2
def baseEnd_1877045 : Nat := 963826295118713786505133

theorem tailTrace_1877045 : CollatzResearch.WordTrace tailWord_1877045 prefixEnd_1877045 963826295118713786505133 := by
  unfold tailWord_1877045
  simp only [CollatzResearch.WordTrace]
  refine ⟨68461455484794013608928589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45640970323196009072619059 68461455484794013608928589)
  ·
    refine ⟨25673045806797755103348221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68461455484794013608928589 25673045806797755103348221)
    ·
      refine ⟨9627392177549158163755583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25673045806797755103348221 9627392177549158163755583)
      ·
        refine ⟨14441088266323737245633375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9627392177549158163755583 14441088266323737245633375)
        ·
          refine ⟨21661632399485605868450063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14441088266323737245633375 21661632399485605868450063)
          ·
            refine ⟨32492448599228408802675095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21661632399485605868450063 32492448599228408802675095)
            ·
              refine ⟨48738672898842613204012643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32492448599228408802675095 48738672898842613204012643)
              ·
                refine ⟨73108009348263919806018965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48738672898842613204012643 73108009348263919806018965)
                ·
                  refine ⟨3426937938199871240907139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73108009348263919806018965 3426937938199871240907139)
                  ·
                    refine ⟨5140406907299806861360709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3426937938199871240907139 5140406907299806861360709)
                    ·
                      refine ⟨963826295118713786505133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5140406907299806861360709 963826295118713786505133)
                      ·
                        rfl

theorem cell23_1877045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1877045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877045 prefixEnd_1877045 := by exact prefixLift 1877045
  have htrace : WordTrace (prefixWord ++ tailWord_1877045) baseStart_1877045 baseEnd_1877045 := by
    simpa [prefixWord, tailWord_1877045, baseEnd_1877045] using wordTrace_append hprefix tailTrace_1877045
  have hstable : (prefixWord ++ tailWord_1877045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877045).length < 2 ^ (prefixWord ++ tailWord_1877045).sum := by decide
  have hdescent : baseEnd_1877045 < baseStart_1877045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877055 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 5, 4]
def baseStart_1877055 : Nat := 118140960795 + 1877055 * 2 ^ 59
def prefixEnd_1877055 : Nat := 4983230072969 + 3 ^ 40 * 1877055 * 2
def baseEnd_1877055 : Nat := 321277143308419582460029

theorem tailTrace_1877055 : CollatzResearch.WordTrace tailWord_1877055 prefixEnd_1877055 321277143308419582460029 := by
  unfold tailWord_1877055
  simp only [CollatzResearch.WordTrace]
  refine ⟨68461820214757785316792619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45641213476505190211195079 68461820214757785316792619)
  ·
    refine ⟨102692730322136677975188929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68461820214757785316792619 102692730322136677975188929)
    ·
      refine ⟨77019547741602508481391697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102692730322136677975188929 77019547741602508481391697)
      ·
        refine ⟨57764660806201881361043773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77019547741602508481391697 57764660806201881361043773)
        ·
          refine ⟨21661747802325705510391415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57764660806201881361043773 21661747802325705510391415)
          ·
            refine ⟨32492621703488558265587123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21661747802325705510391415 32492621703488558265587123)
            ·
              refine ⟨48738932555232837398380685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32492621703488558265587123 48738932555232837398380685)
              ·
                refine ⟨18277099708212314024392757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48738932555232837398380685 18277099708212314024392757)
                ·
                  refine ⟨1713478097644904439786821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18277099708212314024392757 1713478097644904439786821)
                  ·
                    refine ⟨321277143308419582460029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713478097644904439786821 321277143308419582460029)
                    ·
                      rfl

theorem cell23_1877055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 5, 4].length) (baseStart_1877055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877055 prefixEnd_1877055 := by exact prefixLift 1877055
  have htrace : WordTrace (prefixWord ++ tailWord_1877055) baseStart_1877055 baseEnd_1877055 := by
    simpa [prefixWord, tailWord_1877055, baseEnd_1877055] using wordTrace_append hprefix tailTrace_1877055
  have hstable : (prefixWord ++ tailWord_1877055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877055).length < 2 ^ (prefixWord ++ tailWord_1877055).sum := by decide
  have hdescent : baseEnd_1877055 < baseStart_1877055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877096 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1877096 : Nat := 118140960795 + 1877096 * 2 ^ 59
def prefixEnd_1877096 : Nat := 4983230072969 + 3 ^ 40 * 1877096 * 2
def baseEnd_1877096 : Nat := 963852482632093086967399

theorem tailTrace_1877096 : CollatzResearch.WordTrace tailWord_1877096 prefixEnd_1877096 963852482632093086967399 := by
  unfold tailWord_1877096
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231657803804624659517571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45642210405072832879356761 34231657803804624659517571)
  ·
    refine ⟨51347486705706936989276357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34231657803804624659517571 51347486705706936989276357)
    ·
      refine ⟨9627653757320050685489317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51347486705706936989276357 9627653757320050685489317)
      ·
        refine ⟨1805185079497509503529247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9627653757320050685489317 1805185079497509503529247)
        ·
          refine ⟨2707777619246264255293871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805185079497509503529247 2707777619246264255293871)
          ·
            refine ⟨4061666428869396382940807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707777619246264255293871 4061666428869396382940807)
            ·
              refine ⟨6092499643304094574411211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061666428869396382940807 6092499643304094574411211)
              ·
                refine ⟨9138749464956141861616817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6092499643304094574411211 9138749464956141861616817)
                ·
                  refine ⟨6854062098717106396212613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9138749464956141861616817 6854062098717106396212613)
                  ·
                    refine ⟨1285136643509457449289865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854062098717106396212613 1285136643509457449289865)
                    ·
                      refine ⟨963852482632093086967399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285136643509457449289865 963852482632093086967399)
                      ·
                        rfl

theorem cell23_1877096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1877096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877096 prefixEnd_1877096 := by exact prefixLift 1877096
  have htrace : WordTrace (prefixWord ++ tailWord_1877096) baseStart_1877096 baseEnd_1877096 := by
    simpa [prefixWord, tailWord_1877096, baseEnd_1877096] using wordTrace_append hprefix tailTrace_1877096
  have hstable : (prefixWord ++ tailWord_1877096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877096).length < 2 ^ (prefixWord ++ tailWord_1877096).sum := by decide
  have hdescent : baseEnd_1877096 < baseStart_1877096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877102 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_1877102 : Nat := 118140960795 + 1877102 * 2 ^ 59
def prefixEnd_1877102 : Nat := 4983230072969 + 3 ^ 40 * 1877102 * 2
def baseEnd_1877102 : Nat := 107095062612891118165819

theorem tailTrace_1877102 : CollatzResearch.WordTrace tailWord_1877102 prefixEnd_1877102 107095062612891118165819 := by
  unfold tailWord_1877102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557941805698439042969195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45642356297058341562502373 8557941805698439042969195)
  ·
    refine ⟨12836912708547658564453793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8557941805698439042969195 12836912708547658564453793)
    ·
      refine ⟨9627684531410743923340345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12836912708547658564453793 9627684531410743923340345)
      ·
        refine ⟨7220763398558057942505259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9627684531410743923340345 7220763398558057942505259)
        ·
          refine ⟨10831145097837086913757889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220763398558057942505259 10831145097837086913757889)
          ·
            refine ⟨8123358823377815185318417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10831145097837086913757889 8123358823377815185318417)
            ·
              refine ⟨6092519117533361388988813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8123358823377815185318417 6092519117533361388988813)
              ·
                refine ⟨2284694669075010520870805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6092519117533361388988813 2284694669075010520870805)
                ·
                  refine ⟨107095062612891118165819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2284694669075010520870805 107095062612891118165819)
                  ·
                    rfl

theorem cell23_1877102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_1877102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877102 prefixEnd_1877102 := by exact prefixLift 1877102
  have htrace : WordTrace (prefixWord ++ tailWord_1877102) baseStart_1877102 baseEnd_1877102 := by
    simpa [prefixWord, tailWord_1877102, baseEnd_1877102] using wordTrace_append hprefix tailTrace_1877102
  have hstable : (prefixWord ++ tailWord_1877102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877102).length < 2 ^ (prefixWord ++ tailWord_1877102).sum := by decide
  have hdescent : baseEnd_1877102 < baseStart_1877102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877112 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_1877112 : Nat := 118140960795 + 1877112 * 2 ^ 59
def prefixEnd_1877112 : Nat := 4983230072969 + 3 ^ 40 * 1877112 * 2
def baseEnd_1877112 : Nat := 963860698322565024367325

theorem tailTrace_1877112 : CollatzResearch.WordTrace tailWord_1877112 prefixEnd_1877112 963860698322565024367325 := by
  unfold tailWord_1877112
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231949587775642025808795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45642599450367522701078393 34231949587775642025808795)
  ·
    refine ⟨51347924381663463038713193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34231949587775642025808795 51347924381663463038713193)
    ·
      refine ⟨38510943286247597279034895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51347924381663463038713193 38510943286247597279034895)
      ·
        refine ⟨57766414929371395918552343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38510943286247597279034895 57766414929371395918552343)
        ·
          refine ⟨86649622394057093877828515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57766414929371395918552343 86649622394057093877828515)
          ·
            refine ⟨129974433591085640816742773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86649622394057093877828515 129974433591085640816742773)
            ·
              refine ⟨12185103149164278826569635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 129974433591085640816742773 12185103149164278826569635)
              ·
                refine ⟨18277654723746418239854453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12185103149164278826569635 18277654723746418239854453)
                ·
                  refine ⟨1713530130351226709986355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18277654723746418239854453 1713530130351226709986355)
                  ·
                    refine ⟨2570295195526840064979533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713530130351226709986355 2570295195526840064979533)
                    ·
                      refine ⟨963860698322565024367325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570295195526840064979533 963860698322565024367325)
                      ·
                        rfl

theorem cell23_1877112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_1877112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877112 prefixEnd_1877112 := by exact prefixLift 1877112
  have htrace : WordTrace (prefixWord ++ tailWord_1877112) baseStart_1877112 baseEnd_1877112 := by
    simpa [prefixWord, tailWord_1877112, baseEnd_1877112] using wordTrace_append hprefix tailTrace_1877112
  have hstable : (prefixWord ++ tailWord_1877112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877112).length < 2 ^ (prefixWord ++ tailWord_1877112).sum := by decide
  have hdescent : baseEnd_1877112 < baseStart_1877112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877146 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3]
def baseStart_1877146 : Nat := 118140960795 + 1877146 * 2 ^ 59
def prefixEnd_1877146 : Nat := 4983230072969 + 3 ^ 40 * 1877146 * 2
def baseEnd_1877146 : Nat := 963878156664817891342169

theorem tailTrace_1877146 : CollatzResearch.WordTrace tailWord_1877146 prefixEnd_1877146 963878156664817891342169 := by
  unfold tailWord_1877146
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116284814357026964588823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45643426171618738572236861 17116284814357026964588823)
  ·
    refine ⟨25674427221535540446883235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17116284814357026964588823 25674427221535540446883235)
    ·
      refine ⟨38511640832303310670324853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25674427221535540446883235 38511640832303310670324853)
      ·
        refine ⟨3610466328028435375342955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38511640832303310670324853 3610466328028435375342955)
        ·
          refine ⟨5415699492042653063014433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610466328028435375342955 5415699492042653063014433)
          ·
            refine ⟨4061774619031989797260825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5415699492042653063014433 4061774619031989797260825)
            ·
              refine ⟨3046330964273992347945619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4061774619031989797260825 3046330964273992347945619)
              ·
                refine ⟨4569496446410988521918429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046330964273992347945619 4569496446410988521918429)
                ·
                  refine ⟨1713561167404120695719411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4569496446410988521918429 1713561167404120695719411)
                  ·
                    refine ⟨2570341751106181043579117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713561167404120695719411 2570341751106181043579117)
                    ·
                      refine ⟨963878156664817891342169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570341751106181043579117 963878156664817891342169)
                      ·
                        rfl

theorem cell23_1877146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_1877146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877146 prefixEnd_1877146 := by exact prefixLift 1877146
  have htrace : WordTrace (prefixWord ++ tailWord_1877146) baseStart_1877146 baseEnd_1877146 := by
    simpa [prefixWord, tailWord_1877146, baseEnd_1877146] using wordTrace_append hprefix tailTrace_1877146
  have hstable : (prefixWord ++ tailWord_1877146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877146).length < 2 ^ (prefixWord ++ tailWord_1877146).sum := by decide
  have hdescent : baseEnd_1877146 < baseStart_1877146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877169 : List Nat := [1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 4]
def baseStart_1877169 : Nat := 118140960795 + 1877169 * 2 ^ 59
def prefixEnd_1877169 : Nat := 4983230072969 + 3 ^ 40 * 1877169 * 2
def baseEnd_1877169 : Nat := 963889966719871301354563

theorem tailTrace_1877169 : CollatzResearch.WordTrace tailWord_1877169 prefixEnd_1877169 963889966719871301354563 := by
  unfold tailWord_1877169
  simp only [CollatzResearch.WordTrace]
  refine ⟨68465978136344782786442561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45643985424229855190961707 68465978136344782786442561)
  ·
    refine ⟨51349483602258587089831921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68465978136344782786442561 51349483602258587089831921)
    ·
      refine ⟨38512112701693940317373941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51349483602258587089831921 38512112701693940317373941)
      ·
        refine ⟨3610510565783806904753807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38512112701693940317373941 3610510565783806904753807)
        ·
          refine ⟨5415765848675710357130711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610510565783806904753807 5415765848675710357130711)
          ·
            refine ⟨8123648773013565535696067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5415765848675710357130711 8123648773013565535696067)
            ·
              refine ⟨12185473159520348303544101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8123648773013565535696067 12185473159520348303544101)
              ·
                refine ⟨2284776217410065306914519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12185473159520348303544101 2284776217410065306914519)
                ·
                  refine ⟨3427164326115097960371779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284776217410065306914519 3427164326115097960371779)
                  ·
                    refine ⟨5140746489172646940557669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3427164326115097960371779 5140746489172646940557669)
                    ·
                      refine ⟨963889966719871301354563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5140746489172646940557669 963889966719871301354563)
                      ·
                        rfl

theorem cell23_1877169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_1877169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877169 prefixEnd_1877169 := by exact prefixLift 1877169
  have htrace : WordTrace (prefixWord ++ tailWord_1877169) baseStart_1877169 baseEnd_1877169 := by
    simpa [prefixWord, tailWord_1877169, baseEnd_1877169] using wordTrace_append hprefix tailTrace_1877169
  have hstable : (prefixWord ++ tailWord_1877169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877169).length < 2 ^ (prefixWord ++ tailWord_1877169).sum := by decide
  have hdescent : baseEnd_1877169 < baseStart_1877169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877175 : List Nat := [1, 1, 3, 1, 4, 1, 3, 9]
def baseStart_1877175 : Nat := 118140960795 + 1877175 * 2 ^ 59
def prefixEnd_1877175 : Nat := 4983230072969 + 3 ^ 40 * 1877175 * 2
def baseEnd_1877175 : Nat := 35699742503844380662205

theorem tailTrace_1877175 : CollatzResearch.WordTrace tailWord_1877175 prefixEnd_1877175 35699742503844380662205 := by
  unfold tailWord_1877175
  simp only [CollatzResearch.WordTrace]
  refine ⟨68466196974323045811160979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45644131316215363874107319 68466196974323045811160979)
  ·
    refine ⟨102699295461484568716741469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68466196974323045811160979 102699295461484568716741469)
    ·
      refine ⟨38512235798056713268778051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102699295461484568716741469 38512235798056713268778051)
      ·
        refine ⟨57768353697085069903167077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38512235798056713268778051 57768353697085069903167077)
        ·
          refine ⟨10831566318203450606843827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57768353697085069903167077 10831566318203450606843827)
          ·
            refine ⟨16247349477305175910265741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10831566318203450606843827 16247349477305175910265741)
            ·
              refine ⟨6092756053989440966349653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16247349477305175910265741 6092756053989440966349653)
              ·
                refine ⟨35699742503844380662205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6092756053989440966349653 35699742503844380662205)
                ·
                  rfl

theorem cell23_1877175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 9].length) (baseStart_1877175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877175 prefixEnd_1877175 := by exact prefixLift 1877175
  have htrace : WordTrace (prefixWord ++ tailWord_1877175) baseStart_1877175 baseEnd_1877175 := by
    simpa [prefixWord, tailWord_1877175, baseEnd_1877175] using wordTrace_append hprefix tailTrace_1877175
  have hstable : (prefixWord ++ tailWord_1877175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877175).length < 2 ^ (prefixWord ++ tailWord_1877175).sum := by decide
  have hdescent : baseEnd_1877175 < baseStart_1877175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877197 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1877197 : Nat := 118140960795 + 1877197 * 2 ^ 59
def prefixEnd_1877197 : Nat := 4983230072969 + 3 ^ 40 * 1877197 * 2
def baseEnd_1877197 : Nat := 963904344178197191804435

theorem tailTrace_1877197 : CollatzResearch.WordTrace tailWord_1877197 prefixEnd_1877197 963904344178197191804435 := by
  unfold tailWord_1877197
  simp only [CollatzResearch.WordTrace]
  refine ⟨68466999380243343568461845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45644666253495562378974563 68466999380243343568461845)
  ·
    refine ⟨3209390595948906729771649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68466999380243343568461845 3209390595948906729771649)
    ·
      refine ⟨2407042946961680047328737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3209390595948906729771649 2407042946961680047328737)
      ·
        refine ⟨1805282210221260035496553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2407042946961680047328737 1805282210221260035496553)
        ·
          refine ⟨1353961657665945026622415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805282210221260035496553 1353961657665945026622415)
          ·
            refine ⟨2030942486498917539933623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353961657665945026622415 2030942486498917539933623)
            ·
              refine ⟨3046413729748376309900435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030942486498917539933623 3046413729748376309900435)
              ·
                refine ⟨4569620594622564464850653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046413729748376309900435 4569620594622564464850653)
                ·
                  refine ⟨1713607722983461674318995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4569620594622564464850653 1713607722983461674318995)
                  ·
                    refine ⟨2570411584475192511478493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713607722983461674318995 2570411584475192511478493)
                    ·
                      refine ⟨963904344178197191804435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570411584475192511478493 963904344178197191804435)
                      ·
                        rfl

theorem cell23_1877197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1877197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877197 prefixEnd_1877197 := by exact prefixLift 1877197
  have htrace : WordTrace (prefixWord ++ tailWord_1877197) baseStart_1877197 baseEnd_1877197 := by
    simpa [prefixWord, tailWord_1877197, baseEnd_1877197] using wordTrace_append hprefix tailTrace_1877197
  have hstable : (prefixWord ++ tailWord_1877197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877197).length < 2 ^ (prefixWord ++ tailWord_1877197).sum := by decide
  have hdescent : baseEnd_1877197 < baseStart_1877197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877223 : List Nat := [1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1877223 : Nat := 118140960795 + 1877223 * 2 ^ 59
def prefixEnd_1877223 : Nat := 4983230072969 + 3 ^ 40 * 1877223 * 2
def baseEnd_1877223 : Nat := 963917694675214090079315

theorem tailTrace_1877223 : CollatzResearch.WordTrace tailWord_1877223 prefixEnd_1877223 963917694675214090079315 := by
  unfold tailWord_1877223
  simp only [CollatzResearch.WordTrace]
  refine ⟨68467947678149150008908323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45645298452099433339272215 68467947678149150008908323)
  ·
    refine ⟨102701921517223725013362485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68467947678149150008908323 102701921517223725013362485)
    ·
      refine ⟨9628305142239724220002733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102701921517223725013362485 9628305142239724220002733)
      ·
        refine ⟨3610614428339896582501025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9628305142239724220002733 3610614428339896582501025)
        ·
          refine ⟨2707960821254922436875769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3610614428339896582501025 2707960821254922436875769)
          ·
            refine ⟨2030970615941191827656827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707960821254922436875769 2030970615941191827656827)
            ·
              refine ⟨3046455923911787741485241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030970615941191827656827 3046455923911787741485241)
              ·
                refine ⟨2284841942933840806113931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3046455923911787741485241 2284841942933840806113931)
                ·
                  refine ⟨3427262914400761209170897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2284841942933840806113931 3427262914400761209170897)
                  ·
                    refine ⟨2570447185800570906878173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3427262914400761209170897 2570447185800570906878173)
                    ·
                      refine ⟨963917694675214090079315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570447185800570906878173 963917694675214090079315)
                      ·
                        rfl

theorem cell23_1877223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1877223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877223 prefixEnd_1877223 := by exact prefixLift 1877223
  have htrace : WordTrace (prefixWord ++ tailWord_1877223) baseStart_1877223 baseEnd_1877223 := by
    simpa [prefixWord, tailWord_1877223, baseEnd_1877223] using wordTrace_append hprefix tailTrace_1877223
  have hstable : (prefixWord ++ tailWord_1877223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877223).length < 2 ^ (prefixWord ++ tailWord_1877223).sum := by decide
  have hdescent : baseEnd_1877223 < baseStart_1877223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877272 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_1877272 : Nat := 118140960795 + 1877272 * 2 ^ 59
def prefixEnd_1877272 : Nat := 4983230072969 + 3 ^ 40 * 1877272 * 2
def baseEnd_1877272 : Nat := 963942855227284398366589

theorem tailTrace_1877272 : CollatzResearch.WordTrace tailWord_1877272 prefixEnd_1877272 963942855227284398366589 := by
  unfold tailWord_1877272
  simp only [CollatzResearch.WordTrace]
  refine ⟨34234867427485815688721035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45646489903314420918294713 34234867427485815688721035)
  ·
    refine ⟨51352301141228723533081553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34234867427485815688721035 51352301141228723533081553)
    ·
      refine ⟨38514225855921542649811165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51352301141228723533081553 38514225855921542649811165)
      ·
        refine ⟨14442834695970578493679187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38514225855921542649811165 14442834695970578493679187)
        ·
          refine ⟨21664252043955867740518781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442834695970578493679187 21664252043955867740518781)
          ·
            refine ⟨8124094516483450402694543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21664252043955867740518781 8124094516483450402694543)
            ·
              refine ⟨12186141774725175604041815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124094516483450402694543 12186141774725175604041815)
              ·
                refine ⟨18279212662087763406062723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186141774725175604041815 18279212662087763406062723)
                ·
                  refine ⟨27418818993131645109094085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18279212662087763406062723 27418818993131645109094085)
                  ·
                    refine ⟨5141028561212183457955141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27418818993131645109094085 5141028561212183457955141)
                    ·
                      refine ⟨963942855227284398366589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5141028561212183457955141 963942855227284398366589)
                      ·
                        rfl

theorem cell23_1877272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_1877272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877272 prefixEnd_1877272 := by exact prefixLift 1877272
  have htrace : WordTrace (prefixWord ++ tailWord_1877272) baseStart_1877272 baseEnd_1877272 := by
    simpa [prefixWord, tailWord_1877272, baseEnd_1877272] using wordTrace_append hprefix tailTrace_1877272
  have hstable : (prefixWord ++ tailWord_1877272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877272).length < 2 ^ (prefixWord ++ tailWord_1877272).sum := by decide
  have hdescent : baseEnd_1877272 < baseStart_1877272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877292 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 3]
def baseStart_1877292 : Nat := 118140960795 + 1877292 * 2 ^ 59
def prefixEnd_1877292 : Nat := 4983230072969 + 3 ^ 40 * 1877292 * 2
def baseEnd_1877292 : Nat := 963953124840374320116497

theorem tailTrace_1877292 : CollatzResearch.WordTrace tailWord_1877292 prefixEnd_1877292 963953124840374320116497 := by
  unfold tailWord_1877292
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235232157449587396585065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45646976209932783195446753 34235232157449587396585065)
  ·
    refine ⟨25676424118087190547438799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34235232157449587396585065 25676424118087190547438799)
    ·
      refine ⟨38514636177130785821158199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25676424118087190547438799 38514636177130785821158199)
      ·
        refine ⟨57771954265696178731737299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38514636177130785821158199 57771954265696178731737299)
        ·
          refine ⟨86657931398544268097605949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57771954265696178731737299 86657931398544268097605949)
          ·
            refine ⟨32496724274454100536602231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86657931398544268097605949 32496724274454100536602231)
            ·
              refine ⟨48745086411681150804903347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32496724274454100536602231 48745086411681150804903347)
              ·
                refine ⟨73117629617521726207355021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48745086411681150804903347 73117629617521726207355021)
                ·
                  refine ⟨27419111106570647327758133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73117629617521726207355021 27419111106570647327758133)
                  ·
                    refine ⟨2570541666240998186977325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 27419111106570647327758133 2570541666240998186977325)
                    ·
                      refine ⟨963953124840374320116497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570541666240998186977325 963953124840374320116497)
                      ·
                        rfl

theorem cell23_1877292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 3].length) (baseStart_1877292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877292 prefixEnd_1877292 := by exact prefixLift 1877292
  have htrace : WordTrace (prefixWord ++ tailWord_1877292) baseStart_1877292 baseEnd_1877292 := by
    simpa [prefixWord, tailWord_1877292, baseEnd_1877292] using wordTrace_append hprefix tailTrace_1877292
  have hstable : (prefixWord ++ tailWord_1877292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877292).length < 2 ^ (prefixWord ++ tailWord_1877292).sum := by decide
  have hdescent : baseEnd_1877292 < baseStart_1877292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877293 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1877293 : Nat := 118140960795 + 1877293 * 2 ^ 59
def prefixEnd_1877293 : Nat := 4983230072969 + 3 ^ 40 * 1877293 * 2
def baseEnd_1877293 : Nat := 963953638321028816203993

theorem tailTrace_1877293 : CollatzResearch.WordTrace tailWord_1877293 prefixEnd_1877293 963953638321028816203993 := by
  unfold tailWord_1877293
  simp only [CollatzResearch.WordTrace]
  refine ⟨68470500787895551963956533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45647000525263701309304355 68470500787895551963956533)
  ·
    refine ⟨6419109448865207996620925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68470500787895551963956533 6419109448865207996620925)
    ·
      refine ⟨2407166043324452998732847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6419109448865207996620925 2407166043324452998732847)
      ·
        refine ⟨3610749064986679498099271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407166043324452998732847 3610749064986679498099271)
        ·
          refine ⟨5416123597480019247148907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610749064986679498099271 5416123597480019247148907)
          ·
            refine ⟨8124185396220028870723361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416123597480019247148907 8124185396220028870723361)
            ·
              refine ⟨6093139047165021653042521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124185396220028870723361 6093139047165021653042521)
              ·
                refine ⟨4569854285373766239781891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093139047165021653042521 4569854285373766239781891)
                ·
                  refine ⟨6854781428060649359672837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4569854285373766239781891 6854781428060649359672837)
                  ·
                    refine ⟨1285271517761371754938657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6854781428060649359672837 1285271517761371754938657)
                    ·
                      refine ⟨963953638321028816203993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285271517761371754938657 963953638321028816203993)
                      ·
                        rfl

theorem cell23_1877293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1877293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877293 prefixEnd_1877293 := by exact prefixLift 1877293
  have htrace : WordTrace (prefixWord ++ tailWord_1877293) baseStart_1877293 baseEnd_1877293 := by
    simpa [prefixWord, tailWord_1877293, baseEnd_1877293] using wordTrace_append hprefix tailTrace_1877293
  have hstable : (prefixWord ++ tailWord_1877293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877293).length < 2 ^ (prefixWord ++ tailWord_1877293).sum := by decide
  have hdescent : baseEnd_1877293 < baseStart_1877293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877299 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 5]
def baseStart_1877299 : Nat := 118140960795 + 1877299 * 2 ^ 59
def prefixEnd_1877299 : Nat := 4983230072969 + 3 ^ 40 * 1877299 * 2
def baseEnd_1877299 : Nat := 107106302133883976969885

theorem tailTrace_1877299 : CollatzResearch.WordTrace tailWord_1877299 prefixEnd_1877299 107106302133883976969885 := by
  unfold tailWord_1877299
  simp only [CollatzResearch.WordTrace]
  refine ⟨68470719625873814988674951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45647146417249209992449967 68470719625873814988674951)
  ·
    refine ⟨102706079438810722483012427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68470719625873814988674951 102706079438810722483012427)
    ·
      refine ⟨154059119158216083724518641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102706079438810722483012427 154059119158216083724518641)
      ·
        refine ⟨115544339368662062793388981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154059119158216083724518641 115544339368662062793388981)
        ·
          refine ⟨10832281815812068386880217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115544339368662062793388981 10832281815812068386880217)
          ·
            refine ⟨8124211361859051290160163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10832281815812068386880217 8124211361859051290160163)
            ·
              refine ⟨12186317042788576935240245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8124211361859051290160163 12186317042788576935240245)
              ·
                refine ⟨1142467222761429087678773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12186317042788576935240245 1142467222761429087678773)
                ·
                  refine ⟨107106302133883976969885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142467222761429087678773 107106302133883976969885)
                  ·
                    rfl

theorem cell23_1877299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 5].length) (baseStart_1877299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877299 prefixEnd_1877299 := by exact prefixLift 1877299
  have htrace : WordTrace (prefixWord ++ tailWord_1877299) baseStart_1877299 baseEnd_1877299 := by
    simpa [prefixWord, tailWord_1877299, baseEnd_1877299] using wordTrace_append hprefix tailTrace_1877299
  have hstable : (prefixWord ++ tailWord_1877299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877299).length < 2 ^ (prefixWord ++ tailWord_1877299).sum := by decide
  have hdescent : baseEnd_1877299 < baseStart_1877299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877312 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 4, 5]
def baseStart_1877312 : Nat := 118140960795 + 1877312 * 2 ^ 59
def prefixEnd_1877312 : Nat := 4983230072969 + 3 ^ 40 * 1877312 * 2
def baseEnd_1877312 : Nat := 321321131484488080622135

theorem tailTrace_1877312 : CollatzResearch.WordTrace tailWord_1877312 prefixEnd_1877312 321321131484488080622135 := by
  unfold tailWord_1877312
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235596887413359104449095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45647462516551145472598793 34235596887413359104449095)
  ·
    refine ⟨51353395331120038656673643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34235596887413359104449095 51353395331120038656673643)
    ·
      refine ⟨77030092996680057985010465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51353395331120038656673643 77030092996680057985010465)
      ·
        refine ⟨57772569747510043488757849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77030092996680057985010465 57772569747510043488757849)
        ·
          refine ⟨43329427310632532616568387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57772569747510043488757849 43329427310632532616568387)
          ·
            refine ⟨64994140965948798924852581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43329427310632532616568387 64994140965948798924852581)
            ·
              refine ⟨12186401431115399798409859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64994140965948798924852581 12186401431115399798409859)
              ·
                refine ⟨18279602146673099697614789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186401431115399798409859 18279602146673099697614789)
                ·
                  refine ⟨3427425402501206193302773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18279602146673099697614789 3427425402501206193302773)
                  ·
                    refine ⟨321321131484488080622135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3427425402501206193302773 321321131484488080622135)
                    ·
                      rfl

theorem cell23_1877312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 4, 5].length) (baseStart_1877312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877312 prefixEnd_1877312 := by exact prefixLift 1877312
  have htrace : WordTrace (prefixWord ++ tailWord_1877312) baseStart_1877312 baseEnd_1877312 := by
    simpa [prefixWord, tailWord_1877312, baseEnd_1877312] using wordTrace_append hprefix tailTrace_1877312
  have hstable : (prefixWord ++ tailWord_1877312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877312).length < 2 ^ (prefixWord ++ tailWord_1877312).sum := by decide
  have hdescent : baseEnd_1877312 < baseStart_1877312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877316 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 7]
def baseStart_1877316 : Nat := 118140960795 + 1877316 * 2 ^ 59
def prefixEnd_1877316 : Nat := 4983230072969 + 3 ^ 40 * 1877316 * 2
def baseEnd_1877316 : Nat := 107107272041786914024043

theorem tailTrace_1877316 : CollatzResearch.WordTrace tailWord_1877316 prefixEnd_1877316 107107272041786914024043 := by
  unfold tailWord_1877316
  simp only [CollatzResearch.WordTrace]
  refine ⟨34235669833406113446021901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45647559777874817928029201 34235669833406113446021901)
  ·
    refine ⟨12838376187527292542258213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34235669833406113446021901 12838376187527292542258213)
    ·
      refine ⟨2407195535161367351673415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12838376187527292542258213 2407195535161367351673415)
      ·
        refine ⟨3610793302742051027510123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407195535161367351673415 3610793302742051027510123)
        ·
          refine ⟨5416189954113076541265185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610793302742051027510123 5416189954113076541265185)
          ·
            refine ⟨4062142465584807405948889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416189954113076541265185 4062142465584807405948889)
            ·
              refine ⟨3046606849188605554461667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062142465584807405948889 3046606849188605554461667)
              ·
                refine ⟨4569910273782908331692501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046606849188605554461667 4569910273782908331692501)
                ·
                  refine ⟨107107272041786914024043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4569910273782908331692501 107107272041786914024043)
                  ·
                    rfl

theorem cell23_1877316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 7].length) (baseStart_1877316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877316 prefixEnd_1877316 := by exact prefixLift 1877316
  have htrace : WordTrace (prefixWord ++ tailWord_1877316) baseStart_1877316 baseEnd_1877316 := by
    simpa [prefixWord, tailWord_1877316, baseEnd_1877316] using wordTrace_append hprefix tailTrace_1877316
  have hstable : (prefixWord ++ tailWord_1877316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877316).length < 2 ^ (prefixWord ++ tailWord_1877316).sum := by decide
  have hdescent : baseEnd_1877316 < baseStart_1877316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877322 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_1877322 : Nat := 118140960795 + 1877322 * 2 ^ 59
def prefixEnd_1877322 : Nat := 4983230072969 + 3 ^ 40 * 1877322 * 2
def baseEnd_1877322 : Nat := 963968529260009202741359

theorem tailTrace_1877322 : CollatzResearch.WordTrace tailWord_1877322 prefixEnd_1877322 963968529260009202741359 := by
  unfold tailWord_1877322
  simp only [CollatzResearch.WordTrace]
  refine ⟨17117889626197622479190555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45647705669860326611174813 17117889626197622479190555)
  ·
    refine ⟨25676834439296433718785833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17117889626197622479190555 25676834439296433718785833)
    ·
      refine ⟨19257625829472325289089375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25676834439296433718785833 19257625829472325289089375)
      ·
        refine ⟨28886438744208487933634063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19257625829472325289089375 28886438744208487933634063)
        ·
          refine ⟨43329658116312731900451095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28886438744208487933634063 43329658116312731900451095)
          ·
            refine ⟨64994487174469097850676643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43329658116312731900451095 64994487174469097850676643)
            ·
              refine ⟨97491730761703646776014965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64994487174469097850676643 97491730761703646776014965)
              ·
                refine ⟨9139849758909716885251403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97491730761703646776014965 9139849758909716885251403)
                ·
                  refine ⟨13709774638364575327877105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9139849758909716885251403 13709774638364575327877105)
                  ·
                    refine ⟨10282330978773431495907829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13709774638364575327877105 10282330978773431495907829)
                    ·
                      refine ⟨963968529260009202741359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10282330978773431495907829 963968529260009202741359)
                      ·
                        rfl

theorem cell23_1877322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_1877322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877322 prefixEnd_1877322 := by exact prefixLift 1877322
  have htrace : WordTrace (prefixWord ++ tailWord_1877322) baseStart_1877322 baseEnd_1877322 := by
    simpa [prefixWord, tailWord_1877322, baseEnd_1877322] using wordTrace_append hprefix tailTrace_1877322
  have hstable : (prefixWord ++ tailWord_1877322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877322).length < 2 ^ (prefixWord ++ tailWord_1877322).sum := by decide
  have hdescent : baseEnd_1877322 < baseStart_1877322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877349 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1877349 : Nat := 118140960795 + 1877349 * 2 ^ 59
def prefixEnd_1877349 : Nat := 4983230072969 + 3 ^ 40 * 1877349 * 2
def baseEnd_1877349 : Nat := 963982393237680597103735

theorem tailTrace_1877349 : CollatzResearch.WordTrace tailWord_1877349 prefixEnd_1877349 963982393237680597103735 := by
  unfold tailWord_1877349
  simp only [CollatzResearch.WordTrace]
  refine ⟨68472543275692673527995101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45648362183795115685330067 68472543275692673527995101)
  ·
    refine ⟨25677203728384752572998163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68472543275692673527995101 25677203728384752572998163)
    ·
      refine ⟨38515805592577128859497245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25677203728384752572998163 38515805592577128859497245)
      ·
        refine ⟨14443427097216423322311467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38515805592577128859497245 14443427097216423322311467)
        ·
          refine ⟨21665140645824634983467201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14443427097216423322311467 21665140645824634983467201)
          ·
            refine ⟨16248855484368476237600401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21665140645824634983467201 16248855484368476237600401)
            ·
              refine ⟨12186641613276357178200301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16248855484368476237600401 12186641613276357178200301)
              ·
                refine ⟨4569990604978633941825113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12186641613276357178200301 4569990604978633941825113)
                ·
                  refine ⟨3427492953733975456368835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4569990604978633941825113 3427492953733975456368835)
                  ·
                    refine ⟨5141239430600963184553253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3427492953733975456368835 5141239430600963184553253)
                    ·
                      refine ⟨963982393237680597103735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5141239430600963184553253 963982393237680597103735)
                      ·
                        rfl

theorem cell23_1877349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1877349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877349 prefixEnd_1877349 := by exact prefixLift 1877349
  have htrace : WordTrace (prefixWord ++ tailWord_1877349) baseStart_1877349 baseEnd_1877349 := by
    simpa [prefixWord, tailWord_1877349, baseEnd_1877349] using wordTrace_append hprefix tailTrace_1877349
  have hstable : (prefixWord ++ tailWord_1877349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877349).length < 2 ^ (prefixWord ++ tailWord_1877349).sum := by decide
  have hdescent : baseEnd_1877349 < baseStart_1877349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877369 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 3]
def baseStart_1877369 : Nat := 118140960795 + 1877369 * 2 ^ 59
def prefixEnd_1877369 : Nat := 4983230072969 + 3 ^ 40 * 1877369 * 2
def baseEnd_1877369 : Nat := 963992662850770518853643

theorem tailTrace_1877369 : CollatzResearch.WordTrace tailWord_1877369 prefixEnd_1877369 963992662850770518853643 := by
  unfold tailWord_1877369
  simp only [CollatzResearch.WordTrace]
  refine ⟨68473272735620216943723161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45648848490413477962482107 68473272735620216943723161)
  ·
    refine ⟨51354954551715162707792371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68473272735620216943723161 51354954551715162707792371)
    ·
      refine ⟨77032431827572744061688557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51354954551715162707792371 77032431827572744061688557)
      ·
        refine ⟨28887161935339779023133209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77032431827572744061688557 28887161935339779023133209)
        ·
          refine ⟨21665371451504834267349907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28887161935339779023133209 21665371451504834267349907)
          ·
            refine ⟨32498057177257251401024861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21665371451504834267349907 32498057177257251401024861)
            ·
              refine ⟨12186771441471469275384323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32498057177257251401024861 12186771441471469275384323)
              ·
                refine ⟨18280157162207203913076485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12186771441471469275384323 18280157162207203913076485)
                ·
                  refine ⟨3427529467913850733701841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18280157162207203913076485 3427529467913850733701841)
                  ·
                    refine ⟨2570647100935388050276381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3427529467913850733701841 2570647100935388050276381)
                    ·
                      refine ⟨963992662850770518853643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570647100935388050276381 963992662850770518853643)
                      ·
                        rfl

theorem cell23_1877369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 4, 2, 3].length) (baseStart_1877369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877369 prefixEnd_1877369 := by exact prefixLift 1877369
  have htrace : WordTrace (prefixWord ++ tailWord_1877369) baseStart_1877369 baseEnd_1877369 := by
    simpa [prefixWord, tailWord_1877369, baseEnd_1877369] using wordTrace_append hprefix tailTrace_1877369
  have hstable : (prefixWord ++ tailWord_1877369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877369).length < 2 ^ (prefixWord ++ tailWord_1877369).sum := by decide
  have hdescent : baseEnd_1877369 < baseStart_1877369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877372 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 8]
def baseStart_1877372 : Nat := 118140960795 + 1877372 * 2 ^ 59
def prefixEnd_1877372 : Nat := 4983230072969 + 3 ^ 40 * 1877372 * 2
def baseEnd_1877372 : Nat := 107110467032526000790681

theorem tailTrace_1877372 : CollatzResearch.WordTrace tailWord_1877372 prefixEnd_1877372 107110467032526000790681 := by
  unfold tailWord_1877372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34236691077304674228041185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45648921436406232304054913 34236691077304674228041185)
  ·
    refine ⟨25677518307978505671030889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34236691077304674228041185 25677518307978505671030889)
    ·
      refine ⟨19258138730983879253273167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25677518307978505671030889 19258138730983879253273167)
      ·
        refine ⟨28887208096475818879909751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19258138730983879253273167 28887208096475818879909751)
        ·
          refine ⟨43330812144713728319864627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28887208096475818879909751 43330812144713728319864627)
          ·
            refine ⟨64996218217070592479796941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43330812144713728319864627 64996218217070592479796941)
            ·
              refine ⟨24373581831401472179923853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64996218217070592479796941 24373581831401472179923853)
              ·
                refine ⟨9140093186775552067471445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24373581831401472179923853 9140093186775552067471445)
                ·
                  refine ⟨107110467032526000790681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9140093186775552067471445 107110467032526000790681)
                  ·
                    rfl

theorem cell23_1877372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 8].length) (baseStart_1877372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877372 prefixEnd_1877372 := by exact prefixLift 1877372
  have htrace : WordTrace (prefixWord ++ tailWord_1877372) baseStart_1877372 baseEnd_1877372 := by
    simpa [prefixWord, tailWord_1877372, baseEnd_1877372] using wordTrace_append hprefix tailTrace_1877372
  have hstable : (prefixWord ++ tailWord_1877372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877372).length < 2 ^ (prefixWord ++ tailWord_1877372).sum := by decide
  have hdescent : baseEnd_1877372 < baseStart_1877372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877376 : List Nat := [2, 1, 1, 2, 1, 2, 1, 8, 1, 4]
def baseStart_1877376 : Nat := 118140960795 + 1877376 * 2 ^ 59
def prefixEnd_1877376 : Nat := 4983230072969 + 3 ^ 40 * 1877376 * 2
def baseEnd_1877376 : Nat := 321332085738450663822037

theorem tailTrace_1877376 : CollatzResearch.WordTrace tailWord_1877376 prefixEnd_1877376 321332085738450663822037 := by
  unfold tailWord_1877376
  simp only [CollatzResearch.WordTrace]
  refine ⟨34236764023297428569613991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45649018697729904759485321 34236764023297428569613991)
  ·
    refine ⟨51355146034946142854420987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34236764023297428569613991 51355146034946142854420987)
    ·
      refine ⟨77032719052419214281631481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51355146034946142854420987 77032719052419214281631481)
      ·
        refine ⟨57774539289314410711223611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77032719052419214281631481 57774539289314410711223611)
        ·
          refine ⟨86661808933971616066835417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57774539289314410711223611 86661808933971616066835417)
          ·
            refine ⟨64996356700478712050126563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86661808933971616066835417 64996356700478712050126563)
            ·
              refine ⟨97494535050718068075189845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64996356700478712050126563 97494535050718068075189845)
              ·
                refine ⟨1142514082625602360256131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 97494535050718068075189845 1142514082625602360256131)
                ·
                  refine ⟨1713771123938403540384197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142514082625602360256131 1713771123938403540384197)
                  ·
                    refine ⟨321332085738450663822037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713771123938403540384197 321332085738450663822037)
                    ·
                      rfl

theorem cell23_1877376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 1, 4].length) (baseStart_1877376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877376 prefixEnd_1877376 := by exact prefixLift 1877376
  have htrace : WordTrace (prefixWord ++ tailWord_1877376) baseStart_1877376 baseEnd_1877376 := by
    simpa [prefixWord, tailWord_1877376, baseEnd_1877376] using wordTrace_append hprefix tailTrace_1877376
  have hstable : (prefixWord ++ tailWord_1877376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877376).length < 2 ^ (prefixWord ++ tailWord_1877376).sum := by decide
  have hdescent : baseEnd_1877376 < baseStart_1877376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877426 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_1877426 : Nat := 118140960795 + 1877426 * 2 ^ 59
def prefixEnd_1877426 : Nat := 4983230072969 + 3 ^ 40 * 1877426 * 2
def baseEnd_1877426 : Nat := 964021931248076795840881

theorem tailTrace_1877426 : CollatzResearch.WordTrace tailWord_1877426 prefixEnd_1877426 964021931248076795840881 := by
  unfold tailWord_1877426
  simp only [CollatzResearch.WordTrace]
  refine ⟨17118837924103428919637033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45650234464275810452365421 17118837924103428919637033)
  ·
    refine ⟨12839128443077571689727775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17118837924103428919637033 12839128443077571689727775)
    ·
      refine ⟨19258692664616357534591663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12839128443077571689727775 19258692664616357534591663)
      ·
        refine ⟨28888038996924536301887495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19258692664616357534591663 28888038996924536301887495)
        ·
          refine ⟨43332058495386804452831243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28888038996924536301887495 43332058495386804452831243)
          ·
            refine ⟨64998087743080206679246865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43332058495386804452831243 64998087743080206679246865)
            ·
              refine ⟨48748565807310155009435149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64998087743080206679246865 48748565807310155009435149)
              ·
                refine ⟨18280712177741308128538181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48748565807310155009435149 18280712177741308128538181)
                ·
                  refine ⟨3427633533326495274100909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18280712177741308128538181 3427633533326495274100909)
                  ·
                    refine ⟨1285362574997435727787841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3427633533326495274100909 1285362574997435727787841)
                    ·
                      refine ⟨964021931248076795840881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285362574997435727787841 964021931248076795840881)
                      ·
                        rfl

theorem cell23_1877426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_1877426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877426 prefixEnd_1877426 := by exact prefixLift 1877426
  have htrace : WordTrace (prefixWord ++ tailWord_1877426) baseStart_1877426 baseEnd_1877426 := by
    simpa [prefixWord, tailWord_1877426, baseEnd_1877426] using wordTrace_append hprefix tailTrace_1877426
  have hstable : (prefixWord ++ tailWord_1877426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877426).length < 2 ^ (prefixWord ++ tailWord_1877426).sum := by decide
  have hdescent : baseEnd_1877426 < baseStart_1877426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877449 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 6, 4]
def baseStart_1877449 : Nat := 118140960795 + 1877449 * 2 ^ 59
def prefixEnd_1877449 : Nat := 4983230072969 + 3 ^ 40 * 1877449 * 2
def baseEnd_1877449 : Nat := 321344580434376735284425

theorem tailTrace_1877449 : CollatzResearch.WordTrace tailWord_1877449 prefixEnd_1877449 321344580434376735284425 := by
  unfold tailWord_1877449
  simp only [CollatzResearch.WordTrace]
  refine ⟨68476190575330390606635401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45650793716886927071090267 68476190575330390606635401)
  ·
    refine ⟨51357142931497792954976551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68476190575330390606635401 51357142931497792954976551)
    ·
      refine ⟨77035714397246689432464827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51357142931497792954976551 77035714397246689432464827)
      ·
        refine ⟨115553571595870034148697241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77035714397246689432464827 115553571595870034148697241)
        ·
          refine ⟨86665178696902525611522931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115553571595870034148697241 86665178696902525611522931)
          ·
            refine ⟨129997768045353788417284397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86665178696902525611522931 129997768045353788417284397)
            ·
              refine ⟨48749163017007670656481649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129997768045353788417284397 48749163017007670656481649)
              ·
                refine ⟨36561872262755752992361237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48749163017007670656481649 36561872262755752992361237)
                ·
                  refine ⟨1713837762316675921516933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36561872262755752992361237 1713837762316675921516933)
                  ·
                    refine ⟨321344580434376735284425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1713837762316675921516933 321344580434376735284425)
                    ·
                      rfl

theorem cell23_1877449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 6, 4].length) (baseStart_1877449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877449 prefixEnd_1877449 := by exact prefixLift 1877449
  have htrace : WordTrace (prefixWord ++ tailWord_1877449) baseStart_1877449 baseEnd_1877449 := by
    simpa [prefixWord, tailWord_1877449, baseEnd_1877449] using wordTrace_append hprefix tailTrace_1877449
  have hstable : (prefixWord ++ tailWord_1877449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877449).length < 2 ^ (prefixWord ++ tailWord_1877449).sum := by decide
  have hdescent : baseEnd_1877449 < baseStart_1877449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877473 : List Nat := [1, 2, 3, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_1877473 : Nat := 118140960795 + 1877473 * 2 ^ 59
def prefixEnd_1877473 : Nat := 4983230072969 + 3 ^ 40 * 1877473 * 2
def baseEnd_1877473 : Nat := 964046064838838111953165

theorem tailTrace_1877473 : CollatzResearch.WordTrace tailWord_1877473 prefixEnd_1877473 964046064838838111953165 := by
  unfold tailWord_1877473
  simp only [CollatzResearch.WordTrace]
  refine ⟨68477065927243442705509073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45651377284828961803672715 68477065927243442705509073)
  ·
    refine ⟨51357799445432582029131805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68477065927243442705509073 51357799445432582029131805)
    ·
      refine ⟨19259174792037218260924427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51357799445432582029131805 19259174792037218260924427)
      ·
        refine ⟨28888762188055827391386641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19259174792037218260924427 28888762188055827391386641)
        ·
          refine ⟨21666571641041870543539981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28888762188055827391386641 21666571641041870543539981)
          ·
            refine ⟨8124964365390701453827493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21666571641041870543539981 8124964365390701453827493)
            ·
              refine ⟨1523430818510756522592655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8124964365390701453827493 1523430818510756522592655)
              ·
                refine ⟨2285146227766134783888983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523430818510756522592655 2285146227766134783888983)
                ·
                  refine ⟨3427719341649202175833475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285146227766134783888983 3427719341649202175833475)
                  ·
                    refine ⟨5141579012473803263750213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3427719341649202175833475 5141579012473803263750213)
                    ·
                      refine ⟨964046064838838111953165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5141579012473803263750213 964046064838838111953165)
                      ·
                        rfl

theorem cell23_1877473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_1877473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877473 prefixEnd_1877473 := by exact prefixLift 1877473
  have htrace : WordTrace (prefixWord ++ tailWord_1877473) baseStart_1877473 baseEnd_1877473 := by
    simpa [prefixWord, tailWord_1877473, baseEnd_1877473] using wordTrace_append hprefix tailTrace_1877473
  have hstable : (prefixWord ++ tailWord_1877473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877473).length < 2 ^ (prefixWord ++ tailWord_1877473).sum := by decide
  have hdescent : baseEnd_1877473 < baseStart_1877473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877479 : List Nat := [1, 1, 5, 2, 1, 3, 10]
def baseStart_1877479 : Nat := 118140960795 + 1877479 * 2 ^ 59
def prefixEnd_1877479 : Nat := 4983230072969 + 3 ^ 40 * 1877479 * 2
def baseEnd_1877479 : Nat := 11901841305219322079977

theorem tailTrace_1877479 : CollatzResearch.WordTrace tailWord_1877479 prefixEnd_1877479 11901841305219322079977 := by
  unfold tailWord_1877479
  simp only [CollatzResearch.WordTrace]
  refine ⟨68477284765221705730227491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45651523176814470486818327 68477284765221705730227491)
  ·
    refine ⟨102715927147832558595341237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68477284765221705730227491 102715927147832558595341237)
    ·
      refine ⟨9629618170109302368313241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102715927147832558595341237 9629618170109302368313241)
      ·
        refine ⟨7222213627581976776234931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9629618170109302368313241 7222213627581976776234931)
        ·
          refine ⟨10833320441372965164352397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222213627581976776234931 10833320441372965164352397)
          ·
            refine ⟨4062495165514861936632149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10833320441372965164352397 4062495165514861936632149)
            ·
              refine ⟨11901841305219322079977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4062495165514861936632149 11901841305219322079977)
              ·
                rfl

theorem cell23_1877479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 10].length) (baseStart_1877479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877479 prefixEnd_1877479 := by exact prefixLift 1877479
  have htrace : WordTrace (prefixWord ++ tailWord_1877479) baseStart_1877479 baseEnd_1877479 := by
    simpa [prefixWord, tailWord_1877479, baseEnd_1877479] using wordTrace_append hprefix tailTrace_1877479
  have hstable : (prefixWord ++ tailWord_1877479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877479).length < 2 ^ (prefixWord ++ tailWord_1877479).sum := by decide
  have hdescent : baseEnd_1877479 < baseStart_1877479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877490 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_1877490 : Nat := 118140960795 + 1877490 * 2 ^ 59
def prefixEnd_1877490 : Nat := 4983230072969 + 3 ^ 40 * 1877490 * 2
def baseEnd_1877490 : Nat := 964054794009964545440587

theorem tailTrace_1877490 : CollatzResearch.WordTrace tailWord_1877490 prefixEnd_1877490 964054794009964545440587 := by
  unfold tailWord_1877490
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119421492045463652219481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45651790645454569739251949 17119421492045463652219481)
  ·
    refine ⟨12839566119034097739164611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17119421492045463652219481 12839566119034097739164611)
    ·
      refine ⟨19259349178551146608746917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12839566119034097739164611 19259349178551146608746917)
      ·
        refine ⟨3611127970978339989140047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19259349178551146608746917 3611127970978339989140047)
        ·
          refine ⟨5416691956467509983710071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611127970978339989140047 5416691956467509983710071)
          ·
            refine ⟨8125037934701264975565107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416691956467509983710071 8125037934701264975565107)
            ·
              refine ⟨12187556902051897463347661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125037934701264975565107 12187556902051897463347661)
              ·
                refine ⟨4570333838269461548755373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12187556902051897463347661 4570333838269461548755373)
                ·
                  refine ⟨1713875189351048080783265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4570333838269461548755373 1713875189351048080783265)
                  ·
                    refine ⟨1285406392013286060587449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1713875189351048080783265 1285406392013286060587449)
                    ·
                      refine ⟨964054794009964545440587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285406392013286060587449 964054794009964545440587)
                      ·
                        rfl

theorem cell23_1877490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_1877490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877490 prefixEnd_1877490 := by exact prefixLift 1877490
  have htrace : WordTrace (prefixWord ++ tailWord_1877490) baseStart_1877490 baseEnd_1877490 := by
    simpa [prefixWord, tailWord_1877490, baseEnd_1877490] using wordTrace_append hprefix tailTrace_1877490
  have hstable : (prefixWord ++ tailWord_1877490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877490).length < 2 ^ (prefixWord ++ tailWord_1877490).sum := by decide
  have hdescent : baseEnd_1877490 < baseStart_1877490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877493 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1877493 : Nat := 118140960795 + 1877493 * 2 ^ 59
def prefixEnd_1877493 : Nat := 4983230072969 + 3 ^ 40 * 1877493 * 2
def baseEnd_1877493 : Nat := 964056334451928033703073

theorem tailTrace_1877493 : CollatzResearch.WordTrace tailWord_1877493 prefixEnd_1877493 964056334451928033703073 := by
  unfold tailWord_1877493
  simp only [CollatzResearch.WordTrace]
  refine ⟨68477795387170986121237133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45651863591447324080824755 68477795387170986121237133)
  ·
    refine ⟨25679173270189119795463925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68477795387170986121237133 25679173270189119795463925)
    ·
      refine ⟨2407422494080229980824743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25679173270189119795463925 2407422494080229980824743)
      ·
        refine ⟨3611133741120344971237115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2407422494080229980824743 3611133741120344971237115)
        ·
          refine ⟨5416700611680517456855673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611133741120344971237115 5416700611680517456855673)
          ·
            refine ⟨4062525458760388092641755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416700611680517456855673 4062525458760388092641755)
            ·
              refine ⟨6093788188140582138962633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062525458760388092641755 6093788188140582138962633)
              ·
                refine ⟨4570341141105436604221975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6093788188140582138962633 4570341141105436604221975)
                ·
                  refine ⟨6855511711658154906332963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570341141105436604221975 6855511711658154906332963)
                  ·
                    refine ⟨10283267567487232359499445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6855511711658154906332963 10283267567487232359499445)
                    ·
                      refine ⟨964056334451928033703073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10283267567487232359499445 964056334451928033703073)
                      ·
                        rfl

theorem cell23_1877493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1877493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877493 prefixEnd_1877493 := by exact prefixLift 1877493
  have htrace : WordTrace (prefixWord ++ tailWord_1877493) baseStart_1877493 baseEnd_1877493 := by
    simpa [prefixWord, tailWord_1877493, baseEnd_1877493] using wordTrace_append hprefix tailTrace_1877493
  have hstable : (prefixWord ++ tailWord_1877493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877493).length < 2 ^ (prefixWord ++ tailWord_1877493).sum := by decide
  have hdescent : baseEnd_1877493 < baseStart_1877493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877546 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1877546 : Nat := 118140960795 + 1877546 * 2 ^ 59
def prefixEnd_1877546 : Nat := 4983230072969 + 3 ^ 40 * 1877546 * 2
def baseEnd_1877546 : Nat := 964083548926616326340329

theorem tailTrace_1877546 : CollatzResearch.WordTrace tailWord_1877546 prefixEnd_1877546 964083548926616326340329 := by
  unfold tailWord_1877546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119932113994744043229123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45653152303985984115277661 17119932113994744043229123)
  ·
    refine ⟨25679898170992116064843685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17119932113994744043229123 25679898170992116064843685)
    ·
      refine ⟨4814980907061021762158191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25679898170992116064843685 4814980907061021762158191)
      ·
        refine ⟨7222471360591532643237287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4814980907061021762158191 7222471360591532643237287)
        ·
          refine ⟨10833707040887298964855931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222471360591532643237287 10833707040887298964855931)
          ·
            refine ⟨16250560561330948447283897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10833707040887298964855931 16250560561330948447283897)
            ·
              refine ⟨12187920420998211335462923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16250560561330948447283897 12187920420998211335462923)
              ·
                refine ⟨18281880631497317003194385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187920420998211335462923 18281880631497317003194385)
                ·
                  refine ⟨13711410473622987752395789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18281880631497317003194385 13711410473622987752395789)
                  ·
                    refine ⟨5141778927608620407148421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13711410473622987752395789 5141778927608620407148421)
                    ·
                      refine ⟨964083548926616326340329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5141778927608620407148421 964083548926616326340329)
                      ·
                        rfl

theorem cell23_1877546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1877546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877546 prefixEnd_1877546 := by exact prefixLift 1877546
  have htrace : WordTrace (prefixWord ++ tailWord_1877546) baseStart_1877546 baseEnd_1877546 := by
    simpa [prefixWord, tailWord_1877546, baseEnd_1877546] using wordTrace_append hprefix tailTrace_1877546
  have hstable : (prefixWord ++ tailWord_1877546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877546).length < 2 ^ (prefixWord ++ tailWord_1877546).sum := by decide
  have hdescent : baseEnd_1877546 < baseStart_1877546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877557 : List Nat := [1, 3, 3, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_1877557 : Nat := 118140960795 + 1877557 * 2 ^ 59
def prefixEnd_1877557 : Nat := 4983230072969 + 3 ^ 40 * 1877557 * 2
def baseEnd_1877557 : Nat := 964089197213815783302779

theorem tailTrace_1877557 : CollatzResearch.WordTrace tailWord_1877557 prefixEnd_1877557 964089197213815783302779 := by
  unfold tailWord_1877557
  simp only [CollatzResearch.WordTrace]
  refine ⟨68480129658939125051566925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45653419772626083367711283 68480129658939125051566925)
  ·
    refine ⟨25680048622102171894337597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68480129658939125051566925 25680048622102171894337597)
    ·
      refine ⟨9630018233288314460376599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25680048622102171894337597 9630018233288314460376599)
      ·
        refine ⟨14445027349932471690564899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9630018233288314460376599 14445027349932471690564899)
        ·
          refine ⟨21667541024898707535847349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14445027349932471690564899 21667541024898707535847349)
          ·
            refine ⟨2031331971084253831485689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21667541024898707535847349 2031331971084253831485689)
            ·
              refine ⟨1523498978313190373614267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2031331971084253831485689 1523498978313190373614267)
              ·
                refine ⟨2285248467469785560421401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523498978313190373614267 2285248467469785560421401)
                ·
                  refine ⟨1713936350602339170316051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285248467469785560421401 1713936350602339170316051)
                  ·
                    refine ⟨2570904525903508755474077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713936350602339170316051 2570904525903508755474077)
                    ·
                      refine ⟨964089197213815783302779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2570904525903508755474077 964089197213815783302779)
                      ·
                        rfl

theorem cell23_1877557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_1877557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877557 prefixEnd_1877557 := by exact prefixLift 1877557
  have htrace : WordTrace (prefixWord ++ tailWord_1877557) baseStart_1877557 baseEnd_1877557 := by
    simpa [prefixWord, tailWord_1877557, baseEnd_1877557] using wordTrace_append hprefix tailTrace_1877557
  have hstable : (prefixWord ++ tailWord_1877557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877557).length < 2 ^ (prefixWord ++ tailWord_1877557).sum := by decide
  have hdescent : baseEnd_1877557 < baseStart_1877557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877599 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 5, 7]
def baseStart_1877599 : Nat := 118140960795 + 1877599 * 2 ^ 59
def prefixEnd_1877599 : Nat := 4983230072969 + 3 ^ 40 * 1877599 * 2
def baseEnd_1877599 : Nat := 321370254467101539659195

theorem tailTrace_1877599 : CollatzResearch.WordTrace tailWord_1877599 prefixEnd_1877599 321370254467101539659195 := by
  unfold tailWord_1877599
  simp only [CollatzResearch.WordTrace]
  refine ⟨68481661524786966224595851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45654441016524644149730567 68481661524786966224595851)
  ·
    refine ⟨102722492287180449336893777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68481661524786966224595851 102722492287180449336893777)
    ·
      refine ⟨77041869215385337002670333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102722492287180449336893777 77041869215385337002670333)
      ·
        refine ⟨28890700955769501376001375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77041869215385337002670333 28890700955769501376001375)
        ·
          refine ⟨43336051433654252064002063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28890700955769501376001375 43336051433654252064002063)
          ·
            refine ⟨65004077150481378096003095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43336051433654252064002063 65004077150481378096003095)
            ·
              refine ⟨97506115725722067144004643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65004077150481378096003095 97506115725722067144004643)
              ·
                refine ⟨146259173588583100716006965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97506115725722067144004643 146259173588583100716006965)
                ·
                  refine ⟨13711797523929665692125653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 146259173588583100716006965 13711797523929665692125653)
                  ·
                    refine ⟨321370254467101539659195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13711797523929665692125653 321370254467101539659195)
                    ·
                      rfl

theorem cell23_1877599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 7].length) (baseStart_1877599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877599 prefixEnd_1877599 := by exact prefixLift 1877599
  have htrace : WordTrace (prefixWord ++ tailWord_1877599) baseStart_1877599 baseEnd_1877599 := by
    simpa [prefixWord, tailWord_1877599, baseEnd_1877599] using wordTrace_append hprefix tailTrace_1877599
  have hstable : (prefixWord ++ tailWord_1877599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877599).length < 2 ^ (prefixWord ++ tailWord_1877599).sum := by decide
  have hdescent : baseEnd_1877599 < baseStart_1877599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877603 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 5]
def baseStart_1877603 : Nat := 118140960795 + 1877603 * 2 ^ 59
def prefixEnd_1877603 : Nat := 4983230072969 + 3 ^ 40 * 1877603 * 2
def baseEnd_1877603 : Nat := 107123646369324733703063

theorem tailTrace_1877603 : CollatzResearch.WordTrace tailWord_1877603 prefixEnd_1877603 107123646369324733703063 := by
  unfold tailWord_1877603
  simp only [CollatzResearch.WordTrace]
  refine ⟨68481807416772474907741463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45654538277848316605160975 68481807416772474907741463)
  ·
    refine ⟨102722711125158712361612195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68481807416772474907741463 102722711125158712361612195)
    ·
      refine ⟨154084066687738068542418293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102722711125158712361612195 154084066687738068542418293)
      ·
        refine ⟨14445381251975443925851715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154084066687738068542418293 14445381251975443925851715)
        ·
          refine ⟨21668071877963165888777573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14445381251975443925851715 21668071877963165888777573)
          ·
            refine ⟨4062763477118093604145795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21668071877963165888777573 4062763477118093604145795)
            ·
              refine ⟨6094145215677140406218693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4062763477118093604145795 6094145215677140406218693)
              ·
                refine ⟨1142652227939463826166005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6094145215677140406218693 1142652227939463826166005)
                ·
                  refine ⟨107123646369324733703063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1142652227939463826166005 107123646369324733703063)
                  ·
                    rfl

theorem cell23_1877603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 5].length) (baseStart_1877603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877603 prefixEnd_1877603 := by exact prefixLift 1877603
  have htrace : WordTrace (prefixWord ++ tailWord_1877603) baseStart_1877603 baseEnd_1877603 := by
    simpa [prefixWord, tailWord_1877603, baseEnd_1877603] using wordTrace_append hprefix tailTrace_1877603
  have hstable : (prefixWord ++ tailWord_1877603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877603).length < 2 ^ (prefixWord ++ tailWord_1877603).sum := by decide
  have hdescent : baseEnd_1877603 < baseStart_1877603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877633 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 2, 5]
def baseStart_1877633 : Nat := 118140960795 + 1877633 * 2 ^ 59
def prefixEnd_1877633 : Nat := 4983230072969 + 3 ^ 40 * 1877633 * 2
def baseEnd_1877633 : Nat := 321376073914519161984143

theorem tailTrace_1877633 : CollatzResearch.WordTrace tailWord_1877633 prefixEnd_1877633 321376073914519161984143 := by
  unfold tailWord_1877633
  simp only [CollatzResearch.WordTrace]
  refine ⟨68482901606663790031333553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45655267737775860020889035 68482901606663790031333553)
  ·
    refine ⟨51362176204997842523500165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68482901606663790031333553 51362176204997842523500165)
    ·
      refine ⟨9630408038437095473156281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51362176204997842523500165 9630408038437095473156281)
      ·
        refine ⟨7222806028827821604867211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9630408038437095473156281 7222806028827821604867211)
        ·
          refine ⟨10834209043241732407300817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7222806028827821604867211 10834209043241732407300817)
          ·
            refine ⟨8125656782431299305475613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10834209043241732407300817 8125656782431299305475613)
            ·
              refine ⟨3047121293411737239553355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8125656782431299305475613 3047121293411737239553355)
              ·
                refine ⟨4570681940117605859330033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047121293411737239553355 4570681940117605859330033)
                ·
                  refine ⟨3428011455088204394497525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4570681940117605859330033 3428011455088204394497525)
                  ·
                    refine ⟨321376073914519161984143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3428011455088204394497525 321376073914519161984143)
                    ·
                      rfl

theorem cell23_1877633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_1877633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877633 prefixEnd_1877633 := by exact prefixLift 1877633
  have htrace : WordTrace (prefixWord ++ tailWord_1877633) baseStart_1877633 baseEnd_1877633 := by
    simpa [prefixWord, tailWord_1877633, baseEnd_1877633] using wordTrace_append hprefix tailTrace_1877633
  have hstable : (prefixWord ++ tailWord_1877633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877633).length < 2 ^ (prefixWord ++ tailWord_1877633).sum := by decide
  have hdescent : baseEnd_1877633 < baseStart_1877633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877714 : List Nat := [3, 2, 2, 2, 2, 2, 3, 2, 1, 4]
def baseStart_1877714 : Nat := 118140960795 + 1877714 * 2 ^ 59
def prefixEnd_1877714 : Nat := 4983230072969 + 3 ^ 40 * 1877714 * 2
def baseEnd_1877714 : Nat := 321389937892190556346519

theorem tailTrace_1877714 : CollatzResearch.WordTrace tailWord_1877714 prefixEnd_1877714 321389937892190556346519 := by
  unfold tailWord_1877714
  simp only [CollatzResearch.WordTrace]
  refine ⟨17121463979842585216258049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45657237279580227243354797 17121463979842585216258049)
  ·
    refine ⟨12841097984881938912193537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17121463979842585216258049 12841097984881938912193537)
    ·
      refine ⟨9630823488661454184145153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12841097984881938912193537 9630823488661454184145153)
      ·
        refine ⟨7223117616496090638108865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9630823488661454184145153 7223117616496090638108865)
        ·
          refine ⟨5417338212372067978581649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7223117616496090638108865 5417338212372067978581649)
          ·
            refine ⟨4063003659279050983936237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417338212372067978581649 4063003659279050983936237)
            ·
              refine ⟨1523626372229644118976089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4063003659279050983936237 1523626372229644118976089)
              ·
                refine ⟨1142719779172233089232067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523626372229644118976089 1142719779172233089232067)
                ·
                  refine ⟨1714079668758349633848101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142719779172233089232067 1714079668758349633848101)
                  ·
                    refine ⟨321389937892190556346519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714079668758349633848101 321389937892190556346519)
                    ·
                      rfl

theorem cell23_1877714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_1877714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877714 prefixEnd_1877714 := by exact prefixLift 1877714
  have htrace : WordTrace (prefixWord ++ tailWord_1877714) baseStart_1877714 baseEnd_1877714 := by
    simpa [prefixWord, tailWord_1877714, baseEnd_1877714] using wordTrace_append hprefix tailTrace_1877714
  have hstable : (prefixWord ++ tailWord_1877714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877714).length < 2 ^ (prefixWord ++ tailWord_1877714).sum := by decide
  have hdescent : baseEnd_1877714 < baseStart_1877714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877743 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4]
def baseStart_1877743 : Nat := 118140960795 + 1877743 * 2 ^ 59
def prefixEnd_1877743 : Nat := 4983230072969 + 3 ^ 40 * 1877743 * 2
def baseEnd_1877743 : Nat := 964184704615552055576923

theorem tailTrace_1877743 : CollatzResearch.WordTrace tailWord_1877743 prefixEnd_1877743 964184704615552055576923 := by
  unfold tailWord_1877743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68486913636265278817837883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45657942424176852545225255 68486913636265278817837883)
  ·
    refine ⟨102730370454397918226756825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68486913636265278817837883 102730370454397918226756825)
    ·
      refine ⟨77047777840798438670067619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102730370454397918226756825 77047777840798438670067619)
      ·
        refine ⟨115571666761197658005101429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77047777840798438670067619 115571666761197658005101429)
        ·
          refine ⟨10834843758862280437978259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115571666761197658005101429 10834843758862280437978259)
          ·
            refine ⟨16252265638293420656967389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10834843758862280437978259 16252265638293420656967389)
            ·
              refine ⟨6094599614360032746362771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16252265638293420656967389 6094599614360032746362771)
              ·
                refine ⟨9141899421540049119544157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6094599614360032746362771 9141899421540049119544157)
                ·
                  refine ⟨3428212283077518419829059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9141899421540049119544157 3428212283077518419829059)
                  ·
                    refine ⟨5142318424616277629743589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428212283077518419829059 5142318424616277629743589)
                    ·
                      refine ⟨964184704615552055576923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5142318424616277629743589 964184704615552055576923)
                      ·
                        rfl

theorem cell23_1877743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 1, 4].length) (baseStart_1877743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877743 prefixEnd_1877743 := by exact prefixLift 1877743
  have htrace : WordTrace (prefixWord ++ tailWord_1877743) baseStart_1877743 baseEnd_1877743 := by
    simpa [prefixWord, tailWord_1877743, baseEnd_1877743] using wordTrace_append hprefix tailTrace_1877743
  have hstable : (prefixWord ++ tailWord_1877743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877743).length < 2 ^ (prefixWord ++ tailWord_1877743).sum := by decide
  have hdescent : baseEnd_1877743 < baseStart_1877743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877760 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2]
def baseStart_1877760 : Nat := 118140960795 + 1877760 * 2 ^ 59
def prefixEnd_1877760 : Nat := 4983230072969 + 3 ^ 40 * 1877760 * 2
def baseEnd_1877760 : Nat := 964193433786678489064345

theorem tailTrace_1877760 : CollatzResearch.WordTrace tailWord_1877760 prefixEnd_1877760 964193433786678489064345 := by
  unfold tailWord_1877760
  simp only [CollatzResearch.WordTrace]
  refine ⟨34243766838601845360603367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45658355784802460480804489 34243766838601845360603367)
  ·
    refine ⟨51365650257902768040905051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34243766838601845360603367 51365650257902768040905051)
    ·
      refine ⟨77048475386854152061357577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51365650257902768040905051 77048475386854152061357577)
      ·
        refine ⟨57786356540140614046018183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77048475386854152061357577 57786356540140614046018183)
        ·
          refine ⟨86679534810210921069027275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57786356540140614046018183 86679534810210921069027275)
          ·
            refine ⟨130019302215316381603540913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86679534810210921069027275 130019302215316381603540913)
            ·
              refine ⟨97514476661487286202655685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130019302215316381603540913 97514476661487286202655685)
              ·
                refine ⟨18283964374028866162997941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97514476661487286202655685 18283964374028866162997941)
                ·
                  refine ⟨1714121660065206202781057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18283964374028866162997941 1714121660065206202781057)
                  ·
                    refine ⟨1285591245048904652085793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1714121660065206202781057 1285591245048904652085793)
                    ·
                      refine ⟨964193433786678489064345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285591245048904652085793 964193433786678489064345)
                      ·
                        rfl

theorem cell23_1877760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 2, 2].length) (baseStart_1877760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877760 prefixEnd_1877760 := by exact prefixLift 1877760
  have htrace : WordTrace (prefixWord ++ tailWord_1877760) baseStart_1877760 baseEnd_1877760 := by
    simpa [prefixWord, tailWord_1877760, baseEnd_1877760] using wordTrace_append hprefix tailTrace_1877760
  have hstable : (prefixWord ++ tailWord_1877760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877760).length < 2 ^ (prefixWord ++ tailWord_1877760).sum := by decide
  have hdescent : baseEnd_1877760 < baseStart_1877760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877763 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5]
def baseStart_1877763 : Nat := 118140960795 + 1877763 * 2 ^ 59
def prefixEnd_1877763 : Nat := 4983230072969 + 3 ^ 40 * 1877763 * 2
def baseEnd_1877763 : Nat := 964194974228641977326831

theorem tailTrace_1877763 : CollatzResearch.WordTrace tailWord_1877763 prefixEnd_1877763 964194974228641977326831 := by
  unfold tailWord_1877763
  simp only [CollatzResearch.WordTrace]
  refine ⟨68487643096192822233565943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45658428730795214822377295 68487643096192822233565943)
  ·
    refine ⟨102731464644289233350348915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68487643096192822233565943 102731464644289233350348915)
    ·
      refine ⟨154097196966433850025523373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102731464644289233350348915 154097196966433850025523373)
      ·
        refine ⟨57786448862412693759571265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154097196966433850025523373 57786448862412693759571265)
        ·
          refine ⟨43339836646809520319678449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57786448862412693759571265 43339836646809520319678449)
          ·
            refine ⟨32504877485107140239758837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43339836646809520319678449 32504877485107140239758837)
            ·
              refine ⟨3047332264228794397477391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32504877485107140239758837 3047332264228794397477391)
              ·
                refine ⟨4570998396343191596216087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3047332264228794397477391 4570998396343191596216087)
                ·
                  refine ⟨6856497594514787394324131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4570998396343191596216087 6856497594514787394324131)
                  ·
                    refine ⟨10284746391772181091486197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6856497594514787394324131 10284746391772181091486197)
                    ·
                      refine ⟨964194974228641977326831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10284746391772181091486197 964194974228641977326831)
                      ·
                        rfl

theorem cell23_1877763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_1877763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877763 prefixEnd_1877763 := by exact prefixLift 1877763
  have htrace : WordTrace (prefixWord ++ tailWord_1877763) baseStart_1877763 baseEnd_1877763 := by
    simpa [prefixWord, tailWord_1877763, baseEnd_1877763] using wordTrace_append hprefix tailTrace_1877763
  have hstable : (prefixWord ++ tailWord_1877763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877763).length < 2 ^ (prefixWord ++ tailWord_1877763).sum := by decide
  have hdescent : baseEnd_1877763 < baseStart_1877763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877770 : List Nat := [3, 1, 2, 2, 1, 3, 1, 4, 2, 4]
def baseStart_1877770 : Nat := 118140960795 + 1877770 * 2 ^ 59
def prefixEnd_1877770 : Nat := 4983230072969 + 3 ^ 40 * 1877770 * 2
def baseEnd_1877770 : Nat := 321399522864407816646433

theorem tailTrace_1877770 : CollatzResearch.WordTrace tailWord_1877770 prefixEnd_1877770 321399522864407816646433 := by
  unfold tailWord_1877770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17121974601791865607267691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45658598938111641619380509 17121974601791865607267691)
  ·
    refine ⟨25682961902687798410901537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17121974601791865607267691 25682961902687798410901537)
    ·
      refine ⟨19262221427015848808176153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25682961902687798410901537 19262221427015848808176153)
      ·
        refine ⟨14446666070261886606132115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19262221427015848808176153 14446666070261886606132115)
        ·
          refine ⟨21669999105392829909198173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14446666070261886606132115 21669999105392829909198173)
          ·
            refine ⟨8126249664522311215949315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21669999105392829909198173 8126249664522311215949315)
            ·
              refine ⟨12189374496783466823923973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126249664522311215949315 12189374496783466823923973)
              ·
                refine ⟨2285507718146900029485745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12189374496783466823923973 2285507718146900029485745)
                ·
                  refine ⟨1714130788610175022114309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285507718146900029485745 1714130788610175022114309)
                  ·
                    refine ⟨321399522864407816646433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714130788610175022114309 321399522864407816646433)
                    ·
                      rfl

theorem cell23_1877770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 1, 4, 2, 4].length) (baseStart_1877770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877770 prefixEnd_1877770 := by exact prefixLift 1877770
  have htrace : WordTrace (prefixWord ++ tailWord_1877770) baseStart_1877770 baseEnd_1877770 := by
    simpa [prefixWord, tailWord_1877770, baseEnd_1877770] using wordTrace_append hprefix tailTrace_1877770
  have hstable : (prefixWord ++ tailWord_1877770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877770).length < 2 ^ (prefixWord ++ tailWord_1877770).sum := by decide
  have hdescent : baseEnd_1877770 < baseStart_1877770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877783 : List Nat := [1, 1, 3, 4, 2, 1, 3, 8]
def baseStart_1877783 : Nat := 118140960795 + 1877783 * 2 ^ 59
def prefixEnd_1877783 : Nat := 4983230072969 + 3 ^ 40 * 1877783 * 2
def baseEnd_1877783 : Nat := 35711305327471551817657

theorem tailTrace_1877783 : CollatzResearch.WordTrace tailWord_1877783 prefixEnd_1877783 35711305327471551817657 := by
  unfold tailWord_1877783
  simp only [CollatzResearch.WordTrace]
  refine ⟨68488372556120365649294003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45658915037413577099529335 68488372556120365649294003)
  ·
    refine ⟨102732558834180548473941005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68488372556120365649294003 102732558834180548473941005)
    ·
      refine ⟨38524709562817705677727877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102732558834180548473941005 38524709562817705677727877)
      ·
        refine ⟨7223383043028319814573977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38524709562817705677727877 7223383043028319814573977)
        ·
          refine ⟨5417537282271239860930483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7223383043028319814573977 5417537282271239860930483)
          ·
            refine ⟨8126305923406859791395725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417537282271239860930483 8126305923406859791395725)
            ·
              refine ⟨3047364721277572421773397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8126305923406859791395725 3047364721277572421773397)
              ·
                refine ⟨35711305327471551817657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3047364721277572421773397 35711305327471551817657)
                ·
                  rfl

theorem cell23_1877783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 8].length) (baseStart_1877783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877783 prefixEnd_1877783 := by exact prefixLift 1877783
  have htrace : WordTrace (prefixWord ++ tailWord_1877783) baseStart_1877783 baseEnd_1877783 := by
    simpa [prefixWord, tailWord_1877783, baseEnd_1877783] using wordTrace_append hprefix tailTrace_1877783
  have hstable : (prefixWord ++ tailWord_1877783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877783).length < 2 ^ (prefixWord ++ tailWord_1877783).sum := by decide
  have hdescent : baseEnd_1877783 < baseStart_1877783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877800 : List Nat := [2, 1, 5, 1, 1, 3, 3, 7]
def baseStart_1877800 : Nat := 118140960795 + 1877800 * 2 ^ 59
def prefixEnd_1877800 : Nat := 4983230072969 + 3 ^ 40 * 1877800 * 2
def baseEnd_1877800 : Nat := 35711628630105864169043

theorem tailTrace_1877800 : CollatzResearch.WordTrace tailWord_1877800 prefixEnd_1877800 35711628630105864169043 := by
  unfold tailWord_1877800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34244496298529388776331427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45659328398039185035108569 34244496298529388776331427)
  ·
    refine ⟨51366744447794083164497141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34244496298529388776331427 51366744447794083164497141)
    ·
      refine ⟨4815632291980695296671607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51366744447794083164497141 4815632291980695296671607)
      ·
        refine ⟨7223448437971042945007411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815632291980695296671607 7223448437971042945007411)
        ·
          refine ⟨10835172656956564417511117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7223448437971042945007411 10835172656956564417511117)
          ·
            refine ⟨4063189746358711656566669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10835172656956564417511117 4063189746358711656566669)
            ·
              refine ⟨1523696154884516871212501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4063189746358711656566669 1523696154884516871212501)
              ·
                refine ⟨35711628630105864169043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1523696154884516871212501 35711628630105864169043)
                ·
                  rfl

theorem cell23_1877800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 7].length) (baseStart_1877800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877800 prefixEnd_1877800 := by exact prefixLift 1877800
  have htrace : WordTrace (prefixWord ++ tailWord_1877800) baseStart_1877800 baseEnd_1877800 := by
    simpa [prefixWord, tailWord_1877800, baseEnd_1877800] using wordTrace_append hprefix tailTrace_1877800
  have hstable : (prefixWord ++ tailWord_1877800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877800).length < 2 ^ (prefixWord ++ tailWord_1877800).sum := by decide
  have hdescent : baseEnd_1877800 < baseStart_1877800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877810 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1877810 : Nat := 118140960795 + 1877810 * 2 ^ 59
def prefixEnd_1877810 : Nat := 4983230072969 + 3 ^ 40 * 1877810 * 2
def baseEnd_1877810 : Nat := 964219107819403293439115

theorem tailTrace_1877810 : CollatzResearch.WordTrace tailWord_1877810 prefixEnd_1877810 964219107819403293439115 := by
  unfold tailWord_1877810
  simp only [CollatzResearch.WordTrace]
  refine ⟨17122339331755637315131721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45659571551348366173684589 17122339331755637315131721)
  ·
    refine ⟨12841754498816727986348791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17122339331755637315131721 12841754498816727986348791)
    ·
      refine ⟨19262631748225091979523187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12841754498816727986348791 19262631748225091979523187)
      ·
        refine ⟨28893947622337637969284781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19262631748225091979523187 28893947622337637969284781)
        ·
          refine ⟨10835230358376614238481793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28893947622337637969284781 10835230358376614238481793)
          ·
            refine ⟨8126422768782460678861345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10835230358376614238481793 8126422768782460678861345)
            ·
              refine ⟨6094817076586845509146009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8126422768782460678861345 6094817076586845509146009)
              ·
                refine ⟨4571112807440134131859507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6094817076586845509146009 4571112807440134131859507)
                ·
                  refine ⟨6856669211160201197789261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571112807440134131859507 6856669211160201197789261)
                  ·
                    refine ⟨2571250954185075449170973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6856669211160201197789261 2571250954185075449170973)
                    ·
                      refine ⟨964219107819403293439115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2571250954185075449170973 964219107819403293439115)
                      ·
                        rfl

theorem cell23_1877810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1877810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877810 prefixEnd_1877810 := by exact prefixLift 1877810
  have htrace : WordTrace (prefixWord ++ tailWord_1877810) baseStart_1877810 baseEnd_1877810 := by
    simpa [prefixWord, tailWord_1877810, baseEnd_1877810] using wordTrace_append hprefix tailTrace_1877810
  have hstable : (prefixWord ++ tailWord_1877810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877810).length < 2 ^ (prefixWord ++ tailWord_1877810).sum := by decide
  have hdescent : baseEnd_1877810 < baseStart_1877810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877811 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 1, 2, 2]
def baseStart_1877811 : Nat := 118140960795 + 1877811 * 2 ^ 59
def prefixEnd_1877811 : Nat := 4983230072969 + 3 ^ 40 * 1877811 * 2
def baseEnd_1877811 : Nat := 964219621300057789526611

theorem tailTrace_1877811 : CollatzResearch.WordTrace tailWord_1877811 prefixEnd_1877811 964219621300057789526611 := by
  unfold tailWord_1877811
  simp only [CollatzResearch.WordTrace]
  refine ⟨68489393800018926431313287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45659595866679284287542191 68489393800018926431313287)
  ·
    refine ⟨102734090700028389646969931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68489393800018926431313287 102734090700028389646969931)
    ·
      refine ⟨154101136050042584470454897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102734090700028389646969931 154101136050042584470454897)
      ·
        refine ⟨115575852037531938352841173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154101136050042584470454897 115575852037531938352841173)
        ·
          refine ⟨2708809032129654805144715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115575852037531938352841173 2708809032129654805144715)
          ·
            refine ⟨4063213548194482207717073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708809032129654805144715 4063213548194482207717073)
            ·
              refine ⟨3047410161145861655787805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063213548194482207717073 3047410161145861655787805)
              ·
                refine ⟨1142778810429698120920427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3047410161145861655787805 1142778810429698120920427)
                ·
                  refine ⟨1714168215644547181380641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1142778810429698120920427 1714168215644547181380641)
                  ·
                    refine ⟨1285626161733410386035481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1714168215644547181380641 1285626161733410386035481)
                    ·
                      refine ⟨964219621300057789526611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285626161733410386035481 964219621300057789526611)
                      ·
                        rfl

theorem cell23_1877811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 2, 2].length) (baseStart_1877811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877811 prefixEnd_1877811 := by exact prefixLift 1877811
  have htrace : WordTrace (prefixWord ++ tailWord_1877811) baseStart_1877811 baseEnd_1877811 := by
    simpa [prefixWord, tailWord_1877811, baseEnd_1877811] using wordTrace_append hprefix tailTrace_1877811
  have hstable : (prefixWord ++ tailWord_1877811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877811).length < 2 ^ (prefixWord ++ tailWord_1877811).sum := by decide
  have hdescent : baseEnd_1877811 < baseStart_1877811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877814 : List Nat := [5, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1877814 : Nat := 118140960795 + 1877814 * 2 ^ 59
def prefixEnd_1877814 : Nat := 4983230072969 + 3 ^ 40 * 1877814 * 2
def baseEnd_1877814 : Nat := 964221161742021277789097

theorem tailTrace_1877814 : CollatzResearch.WordTrace tailWord_1877814 prefixEnd_1877814 964221161742021277789097 := by
  unfold tailWord_1877814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280593951188003621479531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45659668812672038629114997 4280593951188003621479531)
  ·
    refine ⟨6420890926782005432219297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4280593951188003621479531 6420890926782005432219297)
    ·
      refine ⟨4815668195086504074164473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6420890926782005432219297 4815668195086504074164473)
      ·
        refine ⟨3611751146314878055623355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4815668195086504074164473 3611751146314878055623355)
        ·
          refine ⟨5417626719472317083435033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611751146314878055623355 5417626719472317083435033)
          ·
            refine ⟨4063220039604237812576275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5417626719472317083435033 4063220039604237812576275)
            ·
              refine ⟨6094830059406356718864413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063220039604237812576275 6094830059406356718864413)
              ·
                refine ⟨2285561272277383769574155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6094830059406356718864413 2285561272277383769574155)
                ·
                  refine ⟨3428341908416075654361233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285561272277383769574155 3428341908416075654361233)
                  ·
                    refine ⟨2571256431312056740770925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428341908416075654361233 2571256431312056740770925)
                    ·
                      refine ⟨964221161742021277789097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2571256431312056740770925 964221161742021277789097)
                      ·
                        rfl

theorem cell23_1877814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1877814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877814 prefixEnd_1877814 := by exact prefixLift 1877814
  have htrace : WordTrace (prefixWord ++ tailWord_1877814) baseStart_1877814 baseEnd_1877814 := by
    simpa [prefixWord, tailWord_1877814, baseEnd_1877814] using wordTrace_append hprefix tailTrace_1877814
  have hstable : (prefixWord ++ tailWord_1877814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877814).length < 2 ^ (prefixWord ++ tailWord_1877814).sum := by decide
  have hdescent : baseEnd_1877814 < baseStart_1877814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877827 : List Nat := [1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 3]
def baseStart_1877827 : Nat := 118140960795 + 1877827 * 2 ^ 59
def prefixEnd_1877827 : Nat := 4983230072969 + 3 ^ 40 * 1877827 * 2
def baseEnd_1877827 : Nat := 964227836990529726926537

theorem tailTrace_1877827 : CollatzResearch.WordTrace tailWord_1877827 prefixEnd_1877827 964227836990529726926537 := by
  unfold tailWord_1877827
  simp only [CollatzResearch.WordTrace]
  refine ⟨68489977367960961163895735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45659984911973974109263823 68489977367960961163895735)
  ·
    refine ⟨102734966051941441745843603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68489977367960961163895735 102734966051941441745843603)
    ·
      refine ⟨154102449077912162618765405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102734966051941441745843603 154102449077912162618765405)
      ·
        refine ⟨57788418404217060982037027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154102449077912162618765405 57788418404217060982037027)
        ·
          refine ⟨86682627606325591473055541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57788418404217060982037027 86682627606325591473055541)
          ·
            refine ⟨8126496338093024200598957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86682627606325591473055541 8126496338093024200598957)
            ·
              refine ⟨3047436126784884075224609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8126496338093024200598957 3047436126784884075224609)
              ·
                refine ⟨2285577095088663056418457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047436126784884075224609 2285577095088663056418457)
                ·
                  refine ⟨1714182821316497292313843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2285577095088663056418457 1714182821316497292313843)
                  ·
                    refine ⟨2571274231974745938470765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1714182821316497292313843 2571274231974745938470765)
                    ·
                      refine ⟨964227836990529726926537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2571274231974745938470765 964227836990529726926537)
                      ·
                        rfl

theorem cell23_1877827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_1877827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877827 prefixEnd_1877827 := by exact prefixLift 1877827
  have htrace : WordTrace (prefixWord ++ tailWord_1877827) baseStart_1877827 baseEnd_1877827 := by
    simpa [prefixWord, tailWord_1877827, baseEnd_1877827] using wordTrace_append hprefix tailTrace_1877827
  have hstable : (prefixWord ++ tailWord_1877827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877827).length < 2 ^ (prefixWord ++ tailWord_1877827).sum := by decide
  have hdescent : baseEnd_1877827 < baseStart_1877827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877870 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1877870 : Nat := 118140960795 + 1877870 * 2 ^ 59
def prefixEnd_1877870 : Nat := 4983230072969 + 3 ^ 40 * 1877870 * 2
def baseEnd_1877870 : Nat := 964249916658673058688839

theorem tailTrace_1877870 : CollatzResearch.WordTrace tailWord_1877870 prefixEnd_1877870 964249916658673058688839 := by
  unfold tailWord_1877870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8561443213350647438463883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45661030471203453005140709 8561443213350647438463883)
  ·
    refine ⟨12842164820025971157695825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8561443213350647438463883 12842164820025971157695825)
    ·
      refine ⟨9631623615019478368271869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12842164820025971157695825 9631623615019478368271869)
      ·
        refine ⟨3611858855632304388101951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9631623615019478368271869 3611858855632304388101951)
        ·
          refine ⟨5417788283448456582152927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611858855632304388101951 5417788283448456582152927)
          ·
            refine ⟨8126682425172684873229391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417788283448456582152927 8126682425172684873229391)
            ·
              refine ⟨12190023637759027309844087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8126682425172684873229391 12190023637759027309844087)
              ·
                refine ⟨18285035456638540964766131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12190023637759027309844087 18285035456638540964766131)
                ·
                  refine ⟨27427553184957811447149197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18285035456638540964766131 27427553184957811447149197)
                  ·
                    refine ⟨10285332444359179292680949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27427553184957811447149197 10285332444359179292680949)
                    ·
                      refine ⟨964249916658673058688839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10285332444359179292680949 964249916658673058688839)
                      ·
                        rfl

theorem cell23_1877870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1877870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877870 prefixEnd_1877870 := by exact prefixLift 1877870
  have htrace : WordTrace (prefixWord ++ tailWord_1877870) baseStart_1877870 baseEnd_1877870 := by
    simpa [prefixWord, tailWord_1877870, baseEnd_1877870] using wordTrace_append hprefix tailTrace_1877870
  have hstable : (prefixWord ++ tailWord_1877870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877870).length < 2 ^ (prefixWord ++ tailWord_1877870).sum := by decide
  have hdescent : baseEnd_1877870 < baseStart_1877870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877943 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5]
def baseStart_1877943 : Nat := 118140960795 + 1877943 * 2 ^ 59
def prefixEnd_1877943 : Nat := 4983230072969 + 3 ^ 40 * 1877943 * 2
def baseEnd_1877943 : Nat := 964287400746451273076003

theorem tailTrace_1877943 : CollatzResearch.WordTrace tailWord_1877943 prefixEnd_1877943 964287400746451273076003 := by
  unfold tailWord_1877943
  simp only [CollatzResearch.WordTrace]
  refine ⟨68494208235540712975118483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45662805490360475316745655 68494208235540712975118483)
  ·
    refine ⟨102741312353311069462677725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68494208235540712975118483 102741312353311069462677725)
    ·
      refine ⟨38527992132491651048504147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102741312353311069462677725 38527992132491651048504147)
      ·
        refine ⟨57791988198737476572756221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38527992132491651048504147 57791988198737476572756221)
        ·
          refine ⟨21671995574526553714783583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57791988198737476572756221 21671995574526553714783583)
          ·
            refine ⟨32507993361789830572175375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21671995574526553714783583 32507993361789830572175375)
            ·
              refine ⟨48761990042684745858263063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32507993361789830572175375 48761990042684745858263063)
              ·
                refine ⟨73142985064027118787394595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48761990042684745858263063 73142985064027118787394595)
                ·
                  refine ⟨109714477596040678181091893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73142985064027118787394595 109714477596040678181091893)
                  ·
                    refine ⟨10285732274628813579477365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 109714477596040678181091893 10285732274628813579477365)
                    ·
                      refine ⟨964287400746451273076003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10285732274628813579477365 964287400746451273076003)
                      ·
                        rfl

theorem cell23_1877943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_1877943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877943 prefixEnd_1877943 := by exact prefixLift 1877943
  have htrace : WordTrace (prefixWord ++ tailWord_1877943) baseStart_1877943 baseEnd_1877943 := by
    simpa [prefixWord, tailWord_1877943, baseEnd_1877943] using wordTrace_append hprefix tailTrace_1877943
  have hstable : (prefixWord ++ tailWord_1877943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877943).length < 2 ^ (prefixWord ++ tailWord_1877943).sum := by decide
  have hdescent : baseEnd_1877943 < baseStart_1877943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877974 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1877974 : Nat := 118140960795 + 1877974 * 2 ^ 59
def prefixEnd_1877974 : Nat := 4983230072969 + 3 ^ 40 * 1877974 * 2
def baseEnd_1877974 : Nat := 964303318646740651788361

theorem tailTrace_1877974 : CollatzResearch.WordTrace tailWord_1877974 prefixEnd_1877974 964303318646740651788361 := by
  unfold tailWord_1877974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4280958681151775329343561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45663559265618936846331317 4280958681151775329343561)
  ·
    refine ⟨3210719010863831497007671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4280958681151775329343561 3210719010863831497007671)
    ·
      refine ⟨4816078516295747245511507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3210719010863831497007671 4816078516295747245511507)
      ·
        refine ⟨7224117774443620868267261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816078516295747245511507 7224117774443620868267261)
        ·
          refine ⟨2709044165416357825600223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7224117774443620868267261 2709044165416357825600223)
          ·
            refine ⟨4063566248124536738400335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709044165416357825600223 4063566248124536738400335)
            ·
              refine ⟨6095349372186805107600503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063566248124536738400335 6095349372186805107600503)
              ·
                refine ⟨9143024058280207661400755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095349372186805107600503 9143024058280207661400755)
                ·
                  refine ⟨13714536087420311492101133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143024058280207661400755 13714536087420311492101133)
                  ·
                    refine ⟨5142951032782616809537925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13714536087420311492101133 5142951032782616809537925)
                    ·
                      refine ⟨964303318646740651788361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5142951032782616809537925 964303318646740651788361)
                      ·
                        rfl

theorem cell23_1877974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1877974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877974 prefixEnd_1877974 := by exact prefixLift 1877974
  have htrace : WordTrace (prefixWord ++ tailWord_1877974) baseStart_1877974 baseEnd_1877974 := by
    simpa [prefixWord, tailWord_1877974, baseEnd_1877974] using wordTrace_append hprefix tailTrace_1877974
  have hstable : (prefixWord ++ tailWord_1877974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877974).length < 2 ^ (prefixWord ++ tailWord_1877974).sum := by decide
  have hdescent : baseEnd_1877974 < baseStart_1877974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877977 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 3]
def baseStart_1877977 : Nat := 118140960795 + 1877977 * 2 ^ 59
def prefixEnd_1877977 : Nat := 4983230072969 + 3 ^ 40 * 1877977 * 2
def baseEnd_1877977 : Nat := 964304859088704140050847

theorem tailTrace_1877977 : CollatzResearch.WordTrace tailWord_1877977 prefixEnd_1877977 964304859088704140050847 := by
  unfold tailWord_1877977
  simp only [CollatzResearch.WordTrace]
  refine ⟨68495448317417536781856185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45663632211611691187904123 68495448317417536781856185)
  ·
    refine ⟨51371586238063152586392139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68495448317417536781856185 51371586238063152586392139)
    ·
      refine ⟨77057379357094728879588209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51371586238063152586392139 77057379357094728879588209)
      ·
        refine ⟨57793034517821046659691157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77057379357094728879588209 57793034517821046659691157)
        ·
          refine ⟨2709048493022861562173023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57793034517821046659691157 2709048493022861562173023)
          ·
            refine ⟨4063572739534292343259535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709048493022861562173023 4063572739534292343259535)
            ·
              refine ⟨6095359109301438514889303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063572739534292343259535 6095359109301438514889303)
              ·
                refine ⟨9143038663952157772333955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6095359109301438514889303 9143038663952157772333955)
                ·
                  refine ⟨13714557995928236658500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9143038663952157772333955 13714557995928236658500933)
                  ·
                    refine ⟨2571479624236544373468925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13714557995928236658500933 2571479624236544373468925)
                    ·
                      refine ⟨964304859088704140050847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2571479624236544373468925 964304859088704140050847)
                      ·
                        rfl

theorem cell23_1877977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 1, 4, 3].length) (baseStart_1877977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1877977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1877977 prefixEnd_1877977 := by exact prefixLift 1877977
  have htrace : WordTrace (prefixWord ++ tailWord_1877977) baseStart_1877977 baseEnd_1877977 := by
    simpa [prefixWord, tailWord_1877977, baseEnd_1877977] using wordTrace_append hprefix tailTrace_1877977
  have hstable : (prefixWord ++ tailWord_1877977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877977).length < 2 ^ (prefixWord ++ tailWord_1877977).sum := by decide
  have hdescent : baseEnd_1877977 < baseStart_1877977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878017 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 5, 2]
def baseStart_1878017 : Nat := 118140960795 + 1878017 * 2 ^ 59
def prefixEnd_1878017 : Nat := 4983230072969 + 3 ^ 40 * 1878017 * 2
def baseEnd_1878017 : Nat := 964325398314883983550663

theorem tailTrace_1878017 : CollatzResearch.WordTrace tailWord_1878017 prefixEnd_1878017 964325398314883983550663 := by
  unfold tailWord_1878017
  simp only [CollatzResearch.WordTrace]
  refine ⟨68496907237272623613312305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45664604824848415742208203 68496907237272623613312305)
  ·
    refine ⟨51372680427954467709984229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68496907237272623613312305 51372680427954467709984229)
    ·
      refine ⟨9632377580241462695622043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51372680427954467709984229 9632377580241462695622043)
      ·
        refine ⟨14448566370362194043433065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9632377580241462695622043 14448566370362194043433065)
        ·
          refine ⟨10836424777771645532574799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448566370362194043433065 10836424777771645532574799)
          ·
            refine ⟨16254637166657468298862199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836424777771645532574799 16254637166657468298862199)
            ·
              refine ⟨24381955749986202448293299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16254637166657468298862199 24381955749986202448293299)
              ·
                refine ⟨36572933624979303672439949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24381955749986202448293299 36572933624979303672439949)
                ·
                  refine ⟨13714850109367238877164981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36572933624979303672439949 13714850109367238877164981)
                  ·
                    refine ⟨1285767197753178644734217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13714850109367238877164981 1285767197753178644734217)
                    ·
                      refine ⟨964325398314883983550663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285767197753178644734217 964325398314883983550663)
                      ·
                        rfl

theorem cell23_1878017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_1878017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878017 prefixEnd_1878017 := by exact prefixLift 1878017
  have htrace : WordTrace (prefixWord ++ tailWord_1878017) baseStart_1878017 baseEnd_1878017 := by
    simpa [prefixWord, tailWord_1878017, baseEnd_1878017] using wordTrace_append hprefix tailTrace_1878017
  have hstable : (prefixWord ++ tailWord_1878017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878017).length < 2 ^ (prefixWord ++ tailWord_1878017).sum := by decide
  have hdescent : baseEnd_1878017 < baseStart_1878017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878027 : List Nat := [1, 1, 1, 1, 6, 1, 4, 2, 1, 5]
def baseStart_1878027 : Nat := 118140960795 + 1878027 * 2 ^ 59
def prefixEnd_1878027 : Nat := 4983230072969 + 3 ^ 40 * 1878027 * 2
def baseEnd_1878027 : Nat := 321443511040476314808539

theorem tailTrace_1878027 : CollatzResearch.WordTrace tailWord_1878027 prefixEnd_1878027 321443511040476314808539 := by
  unfold tailWord_1878027
  simp only [CollatzResearch.WordTrace]
  refine ⟨68497271967236395321176335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45664847978157596880784223 68497271967236395321176335)
  ·
    refine ⟨102745907950854592981764503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68497271967236395321176335 102745907950854592981764503)
    ·
      refine ⟨154118861926281889472646755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102745907950854592981764503 154118861926281889472646755)
      ·
        refine ⟨231178292889422834208970133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154118861926281889472646755 231178292889422834208970133)
        ·
          refine ⟨10836482479191695353545475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 231178292889422834208970133 10836482479191695353545475)
          ·
            refine ⟨16254723718787543030318213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836482479191695353545475 16254723718787543030318213)
            ·
              refine ⟨3047760697272664318184665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16254723718787543030318213 3047760697272664318184665)
              ·
                refine ⟨2285820522954498238638499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047760697272664318184665 2285820522954498238638499)
                ·
                  refine ⟨3428730784431747357957749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285820522954498238638499 3428730784431747357957749)
                  ·
                    refine ⟨321443511040476314808539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3428730784431747357957749 321443511040476314808539)
                    ·
                      rfl

theorem cell23_1878027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 5].length) (baseStart_1878027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878027 prefixEnd_1878027 := by exact prefixLift 1878027
  have htrace : WordTrace (prefixWord ++ tailWord_1878027) baseStart_1878027 baseEnd_1878027 := by
    simpa [prefixWord, tailWord_1878027, baseEnd_1878027] using wordTrace_append hprefix tailTrace_1878027
  have hstable : (prefixWord ++ tailWord_1878027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878027).length < 2 ^ (prefixWord ++ tailWord_1878027).sum := by decide
  have hdescent : baseEnd_1878027 < baseStart_1878027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878040 : List Nat := [2, 1, 2, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1878040 : Nat := 118140960795 + 1878040 * 2 ^ 59
def prefixEnd_1878040 : Nat := 4983230072969 + 3 ^ 40 * 1878040 * 2
def baseEnd_1878040 : Nat := 321445736123312464521019

theorem tailTrace_1878040 : CollatzResearch.WordTrace tailWord_1878040 prefixEnd_1878040 321445736123312464521019 := by
  unfold tailWord_1878040
  simp only [CollatzResearch.WordTrace]
  refine ⟨34248873058094649270699787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45665164077459532360933049 34248873058094649270699787)
  ·
    refine ⟨51373309587141973906049681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34248873058094649270699787 51373309587141973906049681)
    ·
      refine ⟨38529982190356480429537261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51373309587141973906049681 38529982190356480429537261)
      ·
        refine ⟨14448743321383680161076473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38529982190356480429537261 14448743321383680161076473)
        ·
          refine ⟨10836557491037760120807355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14448743321383680161076473 10836557491037760120807355)
          ·
            refine ⟨16254836236556640181211033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836557491037760120807355 16254836236556640181211033)
            ·
              refine ⟨12191127177417480135908275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16254836236556640181211033 12191127177417480135908275)
              ·
                refine ⟨18286690766126220203862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12191127177417480135908275 18286690766126220203862413)
                ·
                  refine ⟨6857509037297332576448405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18286690766126220203862413 6857509037297332576448405)
                  ·
                    refine ⟨321445736123312464521019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6857509037297332576448405 321445736123312464521019)
                    ·
                      rfl

theorem cell23_1878040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1878040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878040 prefixEnd_1878040 := by exact prefixLift 1878040
  have htrace : WordTrace (prefixWord ++ tailWord_1878040) baseStart_1878040 baseEnd_1878040 := by
    simpa [prefixWord, tailWord_1878040, baseEnd_1878040] using wordTrace_append hprefix tailTrace_1878040
  have hstable : (prefixWord ++ tailWord_1878040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878040).length < 2 ^ (prefixWord ++ tailWord_1878040).sum := by decide
  have hdescent : baseEnd_1878040 < baseStart_1878040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878047 : List Nat := [1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 4]
def baseStart_1878047 : Nat := 118140960795 + 1878047 * 2 ^ 59
def prefixEnd_1878047 : Nat := 4983230072969 + 3 ^ 40 * 1878047 * 2
def baseEnd_1878047 : Nat := 964340802734518866175525

theorem tailTrace_1878047 : CollatzResearch.WordTrace tailWord_1878047 prefixEnd_1878047 964340802734518866175525 := by
  unfold tailWord_1878047
  simp only [CollatzResearch.WordTrace]
  refine ⟨68498001427163938736904395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45665334284775959157936263 68498001427163938736904395)
  ·
    refine ⟨102747002140745908105356593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68498001427163938736904395 102747002140745908105356593)
    ·
      refine ⟨77060251605559431079017445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102747002140745908105356593 77060251605559431079017445)
      ·
        refine ⟨14448797176042393327315771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77060251605559431079017445 14448797176042393327315771)
        ·
          refine ⟨21673195764063589990973657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14448797176042393327315771 21673195764063589990973657)
          ·
            refine ⟨16254896823047692493230243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21673195764063589990973657 16254896823047692493230243)
            ·
              refine ⟨24382345234571538739845365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16254896823047692493230243 24382345234571538739845365)
              ·
                refine ⟨2285844865741081756860503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24382345234571538739845365 2285844865741081756860503)
                ·
                  refine ⟨3428767298611622635290755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285844865741081756860503 3428767298611622635290755)
                  ·
                    refine ⟨5143150947917433952936133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428767298611622635290755 5143150947917433952936133)
                    ·
                      refine ⟨964340802734518866175525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5143150947917433952936133 964340802734518866175525)
                      ·
                        rfl

theorem cell23_1878047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_1878047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878047 prefixEnd_1878047 := by exact prefixLift 1878047
  have htrace : WordTrace (prefixWord ++ tailWord_1878047) baseStart_1878047 baseEnd_1878047 := by
    simpa [prefixWord, tailWord_1878047, baseEnd_1878047] using wordTrace_append hprefix tailTrace_1878047
  have hstable : (prefixWord ++ tailWord_1878047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878047).length < 2 ^ (prefixWord ++ tailWord_1878047).sum := by decide
  have hdescent : baseEnd_1878047 < baseStart_1878047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878060 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 4]
def baseStart_1878060 : Nat := 118140960795 + 1878060 * 2 ^ 59
def prefixEnd_1878060 : Nat := 4983230072969 + 3 ^ 40 * 1878060 * 2
def baseEnd_1878060 : Nat := 964347477983027315312965

theorem tailTrace_1878060 : CollatzResearch.WordTrace tailWord_1878060 prefixEnd_1878060 964347477983027315312965 := by
  unfold tailWord_1878060
  simp only [CollatzResearch.WordTrace]
  refine ⟨34249237788058420978563817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45665650384077894638085089 34249237788058420978563817)
  ·
    refine ⟨25686928341043815733922863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34249237788058420978563817 25686928341043815733922863)
    ·
      refine ⟨38530392511565723600884295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25686928341043815733922863 38530392511565723600884295)
      ·
        refine ⟨57795588767348585401326443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38530392511565723600884295 57795588767348585401326443)
        ·
          refine ⟨86693383151022878101989665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57795588767348585401326443 86693383151022878101989665)
          ·
            refine ⟨65020037363267158576492249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86693383151022878101989665 65020037363267158576492249)
            ·
              refine ⟨48765028022450368932369187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65020037363267158576492249 48765028022450368932369187)
              ·
                refine ⟨73147542033675553398553781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48765028022450368932369187 73147542033675553398553781)
                ·
                  refine ⟨6857582065657083131114417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73147542033675553398553781 6857582065657083131114417)
                  ·
                    refine ⟨5143186549242812348335813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857582065657083131114417 5143186549242812348335813)
                    ·
                      refine ⟨964347477983027315312965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5143186549242812348335813 964347477983027315312965)
                      ·
                        rfl

theorem cell23_1878060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 4].length) (baseStart_1878060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878060 prefixEnd_1878060 := by exact prefixLift 1878060
  have htrace : WordTrace (prefixWord ++ tailWord_1878060) baseStart_1878060 baseEnd_1878060 := by
    simpa [prefixWord, tailWord_1878060, baseEnd_1878060] using wordTrace_append hprefix tailTrace_1878060
  have hstable : (prefixWord ++ tailWord_1878060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878060).length < 2 ^ (prefixWord ++ tailWord_1878060).sum := by decide
  have hdescent : baseEnd_1878060 < baseStart_1878060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878077 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_1878077 : Nat := 118140960795 + 1878077 * 2 ^ 59
def prefixEnd_1878077 : Nat := 4983230072969 + 3 ^ 40 * 1878077 * 2
def baseEnd_1878077 : Nat := 964356207154153748800387

theorem tailTrace_1878077 : CollatzResearch.WordTrace tailWord_1878077 prefixEnd_1878077 964356207154153748800387 := by
  unfold tailWord_1878077
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499095617055253860496485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45666063744703502573664323 68499095617055253860496485)
  ·
    refine ⟨12843580428197860098843091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68499095617055253860496485 12843580428197860098843091)
    ·
      refine ⟨19265370642296790148264637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12843580428197860098843091 19265370642296790148264637)
      ·
        refine ⟨7224513990861296305599239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19265370642296790148264637 7224513990861296305599239)
        ·
          refine ⟨10836770986291944458398859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224513990861296305599239 10836770986291944458398859)
          ·
            refine ⟨16255156479437916687598289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10836770986291944458398859 16255156479437916687598289)
            ·
              refine ⟨12191367359578437515698717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16255156479437916687598289 12191367359578437515698717)
              ·
                refine ⟨4571762759841914068387019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12191367359578437515698717 4571762759841914068387019)
                ·
                  refine ⟨6857644139762871102580529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4571762759841914068387019 6857644139762871102580529)
                  ·
                    refine ⟨5143233104822153326935397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6857644139762871102580529 5143233104822153326935397)
                    ·
                      refine ⟨964356207154153748800387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5143233104822153326935397 964356207154153748800387)
                      ·
                        rfl

theorem cell23_1878077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_1878077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878077 prefixEnd_1878077 := by exact prefixLift 1878077
  have htrace : WordTrace (prefixWord ++ tailWord_1878077) baseStart_1878077 baseEnd_1878077 := by
    simpa [prefixWord, tailWord_1878077, baseEnd_1878077] using wordTrace_append hprefix tailTrace_1878077
  have hstable : (prefixWord ++ tailWord_1878077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878077).length < 2 ^ (prefixWord ++ tailWord_1878077).sum := by decide
  have hdescent : baseEnd_1878077 < baseStart_1878077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878078 : List Nat := [4, 2, 1, 3, 3, 1, 1, 2, 1, 5]
def baseStart_1878078 : Nat := 118140960795 + 1878078 * 2 ^ 59
def prefixEnd_1878078 : Nat := 4983230072969 + 3 ^ 40 * 1878078 * 2
def baseEnd_1878078 : Nat := 321452240211602748295961

theorem tailTrace_1878078 : CollatzResearch.WordTrace tailWord_1878078 prefixEnd_1878078 321452240211602748295961 := by
  unfold tailWord_1878078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562391511256453878910361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45666088060034420687521925 8562391511256453878910361)
  ·
    refine ⟨6421793633442340409182771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8562391511256453878910361 6421793633442340409182771)
    ·
      refine ⟨9632690450163510613774157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6421793633442340409182771 9632690450163510613774157)
      ·
        refine ⟨3612258918811316480165309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9632690450163510613774157 3612258918811316480165309)
        ·
          refine ⟨1354597094554243680061991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3612258918811316480165309 1354597094554243680061991)
          ·
            refine ⟨2031895641831365520092987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354597094554243680061991 2031895641831365520092987)
            ·
              refine ⟨3047843462747048280139481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031895641831365520092987 3047843462747048280139481)
              ·
                refine ⟨2285882597060286210104611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047843462747048280139481 2285882597060286210104611)
                ·
                  refine ⟨3428823895590429315156917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285882597060286210104611 3428823895590429315156917)
                  ·
                    refine ⟨321452240211602748295961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3428823895590429315156917 321452240211602748295961)
                    ·
                      rfl

theorem cell23_1878078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_1878078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878078 prefixEnd_1878078 := by exact prefixLift 1878078
  have htrace : WordTrace (prefixWord ++ tailWord_1878078) baseStart_1878078 baseEnd_1878078 := by
    simpa [prefixWord, tailWord_1878078, baseEnd_1878078] using wordTrace_append hprefix tailTrace_1878078
  have hstable : (prefixWord ++ tailWord_1878078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878078).length < 2 ^ (prefixWord ++ tailWord_1878078).sum := by decide
  have hdescent : baseEnd_1878078 < baseStart_1878078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878081 : List Nat := [1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 4]
def baseStart_1878081 : Nat := 118140960795 + 1878081 * 2 ^ 59
def prefixEnd_1878081 : Nat := 4983230072969 + 3 ^ 40 * 1878081 * 2
def baseEnd_1878081 : Nat := 964358261076771733150369

theorem tailTrace_1878081 : CollatzResearch.WordTrace tailWord_1878081 prefixEnd_1878081 964358261076771733150369 := by
  unfold tailWord_1878081
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499241509040762543642097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45666161006027175029094731 68499241509040762543642097)
  ·
    refine ⟨51374431131780571907731573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68499241509040762543642097 51374431131780571907731573)
    ·
      refine ⟨4816352918604428616349835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51374431131780571907731573 4816352918604428616349835)
      ·
        refine ⟨7224529377906642924524753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816352918604428616349835 7224529377906642924524753)
        ·
          refine ⟨5418397033429982193393565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7224529377906642924524753 5418397033429982193393565)
          ·
            refine ⟨2031898887536243322522587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5418397033429982193393565 2031898887536243322522587)
            ·
              refine ⟨3047848331304364983783881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031898887536243322522587 3047848331304364983783881)
              ·
                refine ⟨2285886248478273737837911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047848331304364983783881 2285886248478273737837911)
                ·
                  refine ⟨3428829372717410606756867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285886248478273737837911 3428829372717410606756867)
                  ·
                    refine ⟨5143244059076115910135301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3428829372717410606756867 5143244059076115910135301)
                    ·
                      refine ⟨964358261076771733150369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5143244059076115910135301 964358261076771733150369)
                      ·
                        rfl

theorem cell23_1878081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_1878081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878081 prefixEnd_1878081 := by exact prefixLift 1878081
  have htrace : WordTrace (prefixWord ++ tailWord_1878081) baseStart_1878081 baseEnd_1878081 := by
    simpa [prefixWord, tailWord_1878081, baseEnd_1878081] using wordTrace_append hprefix tailTrace_1878081
  have hstable : (prefixWord ++ tailWord_1878081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878081).length < 2 ^ (prefixWord ++ tailWord_1878081).sum := by decide
  have hdescent : baseEnd_1878081 < baseStart_1878081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878101 : List Nat := [1, 3, 2, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1878101 : Nat := 118140960795 + 1878101 * 2 ^ 59
def prefixEnd_1878101 : Nat := 4983230072969 + 3 ^ 40 * 1878101 * 2
def baseEnd_1878101 : Nat := 964368530689861654900277

theorem tailTrace_1878101 : CollatzResearch.WordTrace tailWord_1878101 prefixEnd_1878101 964368530689861654900277 := by
  unfold tailWord_1878101
  simp only [CollatzResearch.WordTrace]
  refine ⟨68499970968968305959370157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45666647312645537306246771 68499970968968305959370157)
  ·
    refine ⟨25687489113363114734763809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68499970968968305959370157 25687489113363114734763809)
    ·
      refine ⟨19265616835022336051072857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25687489113363114734763809 19265616835022336051072857)
      ·
        refine ⟨14449212626266752038304643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19265616835022336051072857 14449212626266752038304643)
        ·
          refine ⟨21673818939400128057456965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14449212626266752038304643 21673818939400128057456965)
          ·
            refine ⟨4063841051137524010773181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21673818939400128057456965 4063841051137524010773181)
            ·
              refine ⟨1523940394176571504039943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4063841051137524010773181 1523940394176571504039943)
              ·
                refine ⟨2285910591264857256059915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523940394176571504039943 2285910591264857256059915)
                ·
                  refine ⟨3428865886897285884089873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285910591264857256059915 3428865886897285884089873)
                  ·
                    refine ⟨2571649415172964413067405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3428865886897285884089873 2571649415172964413067405)
                    ·
                      refine ⟨964368530689861654900277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2571649415172964413067405 964368530689861654900277)
                      ·
                        rfl

theorem cell23_1878101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1878101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878101 prefixEnd_1878101 := by exact prefixLift 1878101
  have htrace : WordTrace (prefixWord ++ tailWord_1878101) baseStart_1878101 baseEnd_1878101 := by
    simpa [prefixWord, tailWord_1878101, baseEnd_1878101] using wordTrace_append hprefix tailTrace_1878101
  have hstable : (prefixWord ++ tailWord_1878101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878101).length < 2 ^ (prefixWord ++ tailWord_1878101).sum := by decide
  have hdescent : baseEnd_1878101 < baseStart_1878101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878124 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 3, 3, 2]
def baseStart_1878124 : Nat := 118140960795 + 1878124 * 2 ^ 59
def prefixEnd_1878124 : Nat := 4983230072969 + 3 ^ 40 * 1878124 * 2
def baseEnd_1878124 : Nat := 964380340744915064912671

theorem tailTrace_1878124 : CollatzResearch.WordTrace tailWord_1878124 prefixEnd_1878124 964380340744915064912671 := by
  unfold tailWord_1878124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34250404923942490443728713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45667206565256653924971617 34250404923942490443728713)
  ·
    refine ⟨25687803692956867832796535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34250404923942490443728713 25687803692956867832796535)
    ·
      refine ⟨38531705539435301749194803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25687803692956867832796535 38531705539435301749194803)
      ·
        refine ⟨57797558309152952623792205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38531705539435301749194803 57797558309152952623792205)
        ·
          refine ⟨21674084365932357233922077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57797558309152952623792205 21674084365932357233922077)
          ·
            refine ⟨8127781637224633962720779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21674084365932357233922077 8127781637224633962720779)
            ·
              refine ⟨12191672455836950944081169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8127781637224633962720779 12191672455836950944081169)
              ·
                refine ⟨9143754341877713208060877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12191672455836950944081169 9143754341877713208060877)
                ·
                  refine ⟨3428907878204142453022829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9143754341877713208060877 3428907878204142453022829)
                  ·
                    refine ⟨1285840454326553419883561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3428907878204142453022829 1285840454326553419883561)
                    ·
                      refine ⟨964380340744915064912671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285840454326553419883561 964380340744915064912671)
                      ·
                        rfl

theorem cell23_1878124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 3, 2].length) (baseStart_1878124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878124 prefixEnd_1878124 := by exact prefixLift 1878124
  have htrace : WordTrace (prefixWord ++ tailWord_1878124) baseStart_1878124 baseEnd_1878124 := by
    simpa [prefixWord, tailWord_1878124, baseEnd_1878124] using wordTrace_append hprefix tailTrace_1878124
  have hstable : (prefixWord ++ tailWord_1878124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878124).length < 2 ^ (prefixWord ++ tailWord_1878124).sum := by decide
  have hdescent : baseEnd_1878124 < baseStart_1878124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878158 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1878158 : Nat := 118140960795 + 1878158 * 2 ^ 59
def prefixEnd_1878158 : Nat := 4983230072969 + 3 ^ 40 * 1878158 * 2
def baseEnd_1878158 : Nat := 964397799087167931887515

theorem tailTrace_1878158 : CollatzResearch.WordTrace tailWord_1878158 prefixEnd_1878158 964397799087167931887515 := by
  unfold tailWord_1878158
  simp only [CollatzResearch.WordTrace]
  refine ⟨8562756241220225586774391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45668033286507869796130085 8562756241220225586774391)
  ·
    refine ⟨12844134361830338380161587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8562756241220225586774391 12844134361830338380161587)
    ·
      refine ⟨19266201542745507570242381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12844134361830338380161587 19266201542745507570242381)
      ·
        refine ⟨7224825578529565338840893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19266201542745507570242381 7224825578529565338840893)
        ·
          refine ⟨2709309591948587002065335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7224825578529565338840893 2709309591948587002065335)
          ·
            refine ⟨4063964387922880503098003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709309591948587002065335 4063964387922880503098003)
            ·
              refine ⟨6095946581884320754647005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063964387922880503098003 6095946581884320754647005)
              ·
                refine ⟨2285979968206620282992627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6095946581884320754647005 2285979968206620282992627)
                ·
                  refine ⟨3428969952309930424488941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2285979968206620282992627 3428969952309930424488941)
                  ·
                    refine ⟨1285863732116223909183353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3428969952309930424488941 1285863732116223909183353)
                    ·
                      refine ⟨964397799087167931887515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285863732116223909183353 964397799087167931887515)
                      ·
                        rfl

theorem cell23_1878158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1878158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878158 prefixEnd_1878158 := by exact prefixLift 1878158
  have htrace : WordTrace (prefixWord ++ tailWord_1878158) baseStart_1878158 baseEnd_1878158 := by
    simpa [prefixWord, tailWord_1878158, baseEnd_1878158] using wordTrace_append hprefix tailTrace_1878158
  have hstable : (prefixWord ++ tailWord_1878158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878158).length < 2 ^ (prefixWord ++ tailWord_1878158).sum := by decide
  have hdescent : baseEnd_1878158 < baseStart_1878158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878160 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 9]
def baseStart_1878160 : Nat := 118140960795 + 1878160 * 2 ^ 59
def prefixEnd_1878160 : Nat := 4983230072969 + 3 ^ 40 * 1878160 * 2
def baseEnd_1878160 : Nat := 107155425116497436006945

theorem tailTrace_1878160 : CollatzResearch.WordTrace tailWord_1878160 prefixEnd_1878160 107155425116497436006945 := by
  unfold tailWord_1878160
  simp only [CollatzResearch.WordTrace]
  refine ⟨34251061437877279517883967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45668081917169706023845289 34251061437877279517883967)
  ·
    refine ⟨51376592156815919276825951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34251061437877279517883967 51376592156815919276825951)
    ·
      refine ⟨77064888235223878915238927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51376592156815919276825951 77064888235223878915238927)
      ·
        refine ⟨115597332352835818372858391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77064888235223878915238927 115597332352835818372858391)
        ·
          refine ⟨173395998529253727559287587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115597332352835818372858391 173395998529253727559287587)
          ·
            refine ⟨260093997793880591338931381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173395998529253727559287587 260093997793880591338931381)
            ·
              refine ⟨24383812293176305438024817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 260093997793880591338931381 24383812293176305438024817)
              ·
                refine ⟨18287859219882229078518613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24383812293176305438024817 18287859219882229078518613)
                ·
                  refine ⟨107155425116497436006945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 18287859219882229078518613 107155425116497436006945)
                  ·
                    rfl

theorem cell23_1878160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 9].length) (baseStart_1878160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878160 prefixEnd_1878160 := by exact prefixLift 1878160
  have htrace : WordTrace (prefixWord ++ tailWord_1878160) baseStart_1878160 baseEnd_1878160 := by
    simpa [prefixWord, tailWord_1878160, baseEnd_1878160] using wordTrace_append hprefix tailTrace_1878160
  have hstable : (prefixWord ++ tailWord_1878160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878160).length < 2 ^ (prefixWord ++ tailWord_1878160).sum := by decide
  have hdescent : baseEnd_1878160 < baseStart_1878160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878177 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 7]
def baseStart_1878177 : Nat := 118140960795 + 1878177 * 2 ^ 59
def prefixEnd_1878177 : Nat := 4983230072969 + 3 ^ 40 * 1878177 * 2
def baseEnd_1878177 : Nat := 107156395024400373061103

theorem tailTrace_1878177 : CollatzResearch.WordTrace tailWord_1878177 prefixEnd_1878177 107156395024400373061103 := by
  unfold tailWord_1878177
  simp only [CollatzResearch.WordTrace]
  refine ⟨68502742916692970939136785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45668495277795313959424523 68502742916692970939136785)
  ·
    refine ⟨51377057187519728204352589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68502742916692970939136785 51377057187519728204352589)
    ·
      refine ⟨19266396445319898076632221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51377057187519728204352589 19266396445319898076632221)
      ·
        refine ⟨7224898666994961778737083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19266396445319898076632221 7224898666994961778737083)
        ·
          refine ⟨10837348000492442668105625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224898666994961778737083 10837348000492442668105625)
          ·
            refine ⟨8128011000369332001079219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10837348000492442668105625 8128011000369332001079219)
            ·
              refine ⟨12192016500553998001618829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8128011000369332001079219 12192016500553998001618829)
              ·
                refine ⟨4572006187707749250607061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12192016500553998001618829 4572006187707749250607061)
                ·
                  refine ⟨107156395024400373061103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4572006187707749250607061 107156395024400373061103)
                  ·
                    rfl

theorem cell23_1878177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 7].length) (baseStart_1878177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878177 prefixEnd_1878177 := by exact prefixLift 1878177
  have htrace : WordTrace (prefixWord ++ tailWord_1878177) baseStart_1878177 baseEnd_1878177 := by
    simpa [prefixWord, tailWord_1878177, baseEnd_1878177] using wordTrace_append hprefix tailTrace_1878177
  have hstable : (prefixWord ++ tailWord_1878177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878177).length < 2 ^ (prefixWord ++ tailWord_1878177).sum := by decide
  have hdescent : baseEnd_1878177 < baseStart_1878177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878207 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 2, 5]
def baseStart_1878207 : Nat := 118140960795 + 1878207 * 2 ^ 59
def prefixEnd_1878207 : Nat := 4983230072969 + 3 ^ 40 * 1878207 * 2
def baseEnd_1878207 : Nat := 321474319879746080058263

theorem tailTrace_1878207 : CollatzResearch.WordTrace tailWord_1878207 prefixEnd_1878207 321474319879746080058263 := by
  unfold tailWord_1878207
  simp only [CollatzResearch.WordTrace]
  refine ⟨68503837106584286062728875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45669224737722857375152583 68503837106584286062728875)
  ·
    refine ⟨102755755659876429094093313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68503837106584286062728875 102755755659876429094093313)
    ·
      refine ⟨77066816744907321820569985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102755755659876429094093313 77066816744907321820569985)
      ·
        refine ⟨57800112558680491365427489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77066816744907321820569985 57800112558680491365427489)
        ·
          refine ⟨43350084419010368524070617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57800112558680491365427489 43350084419010368524070617)
          ·
            refine ⟨32512563314257776393052963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43350084419010368524070617 32512563314257776393052963)
            ·
              refine ⟨48768844971386664589579445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32512563314257776393052963 48768844971386664589579445)
              ·
                refine ⟨4572079216067499805273073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48768844971386664589579445 4572079216067499805273073)
                ·
                  refine ⟨3429059412050624853954805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4572079216067499805273073 3429059412050624853954805)
                  ·
                    refine ⟨321474319879746080058263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3429059412050624853954805 321474319879746080058263)
                    ·
                      rfl

theorem cell23_1878207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 5].length) (baseStart_1878207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878207 prefixEnd_1878207 := by exact prefixLift 1878207
  have htrace : WordTrace (prefixWord ++ tailWord_1878207) baseStart_1878207 baseEnd_1878207 := by
    simpa [prefixWord, tailWord_1878207, baseEnd_1878207] using wordTrace_append hprefix tailTrace_1878207
  have hstable : (prefixWord ++ tailWord_1878207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878207).length < 2 ^ (prefixWord ++ tailWord_1878207).sum := by decide
  have hdescent : baseEnd_1878207 < baseStart_1878207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878244 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 6, 2]
def baseStart_1878244 : Nat := 118140960795 + 1878244 * 2 ^ 59
def prefixEnd_1878244 : Nat := 4983230072969 + 3 ^ 40 * 1878244 * 2
def baseEnd_1878244 : Nat := 964441958423454595412119

theorem tailTrace_1878244 : CollatzResearch.WordTrace tailWord_1878244 prefixEnd_1878244 964441958423454595412119 := by
  unfold tailWord_1878244
  simp only [CollatzResearch.WordTrace]
  refine ⟨34252593303725120690912893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45670124404966827587883857 34252593303725120690912893)
  ·
    refine ⟨12844722488896920259092335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34252593303725120690912893 12844722488896920259092335)
    ·
      refine ⟨19267083733345380388638503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12844722488896920259092335 19267083733345380388638503)
      ·
        refine ⟨28900625600018070582957755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19267083733345380388638503 28900625600018070582957755)
        ·
          refine ⟨43350938400027105874436633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28900625600018070582957755 43350938400027105874436633)
          ·
            refine ⟨32513203800020329405827475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43350938400027105874436633 32513203800020329405827475)
            ·
              refine ⟨48769805700030494108741213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32513203800020329405827475 48769805700030494108741213)
              ·
                refine ⟨18288677137511435290777955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48769805700030494108741213 18288677137511435290777955)
                ·
                  refine ⟨27433015706267152936166933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18288677137511435290777955 27433015706267152936166933)
                  ·
                    refine ⟨1285922611231272793882825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27433015706267152936166933 1285922611231272793882825)
                    ·
                      refine ⟨964441958423454595412119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1285922611231272793882825 964441958423454595412119)
                      ·
                        rfl

theorem cell23_1878244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 6, 2].length) (baseStart_1878244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878244 prefixEnd_1878244 := by exact prefixLift 1878244
  have htrace : WordTrace (prefixWord ++ tailWord_1878244) baseStart_1878244 baseEnd_1878244 := by
    simpa [prefixWord, tailWord_1878244, baseEnd_1878244] using wordTrace_append hprefix tailTrace_1878244
  have hstable : (prefixWord ++ tailWord_1878244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878244).length < 2 ^ (prefixWord ++ tailWord_1878244).sum := by decide
  have hdescent : baseEnd_1878244 < baseStart_1878244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878254 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 5, 4]
def baseStart_1878254 : Nat := 118140960795 + 1878254 * 2 ^ 59
def prefixEnd_1878254 : Nat := 4983230072969 + 3 ^ 40 * 1878254 * 2
def baseEnd_1878254 : Nat := 321482364409999852095691

theorem tailTrace_1878254 : CollatzResearch.WordTrace tailWord_1878254 prefixEnd_1878254 321482364409999852095691 := by
  unfold tailWord_1878254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563193917176751636211227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45670367558276008726459877 8563193917176751636211227)
  ·
    refine ⟨12844790875765127454316841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563193917176751636211227 12844790875765127454316841)
    ·
      refine ⟨9633593156823845590737631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12844790875765127454316841 9633593156823845590737631)
      ·
        refine ⟨14450389735235768386106447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9633593156823845590737631 14450389735235768386106447)
        ·
          refine ⟨21675584602853652579159671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14450389735235768386106447 21675584602853652579159671)
          ·
            refine ⟨32513376904280478868739507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21675584602853652579159671 32513376904280478868739507)
            ·
              refine ⟨48770065356420718303109261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32513376904280478868739507 48770065356420718303109261)
              ·
                refine ⟨18288774508657769363665973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48770065356420718303109261 18288774508657769363665973)
                ·
                  refine ⟨1714572610186665877843685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 18288774508657769363665973 1714572610186665877843685)
                  ·
                    refine ⟨321482364409999852095691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714572610186665877843685 321482364409999852095691)
                    ·
                      rfl

theorem cell23_1878254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 5, 4].length) (baseStart_1878254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878254 prefixEnd_1878254 := by exact prefixLift 1878254
  have htrace : WordTrace (prefixWord ++ tailWord_1878254) baseStart_1878254 baseEnd_1878254 := by
    simpa [prefixWord, tailWord_1878254, baseEnd_1878254] using wordTrace_append hprefix tailTrace_1878254
  have hstable : (prefixWord ++ tailWord_1878254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878254).length < 2 ^ (prefixWord ++ tailWord_1878254).sum := by decide
  have hdescent : baseEnd_1878254 < baseStart_1878254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878257 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1878257 : Nat := 118140960795 + 1878257 * 2 ^ 59
def prefixEnd_1878257 : Nat := 4983230072969 + 3 ^ 40 * 1878257 * 2
def baseEnd_1878257 : Nat := 964448633671963044549559

theorem tailTrace_1878257 : CollatzResearch.WordTrace tailWord_1878257 prefixEnd_1878257 964448633671963044549559 := by
  unfold tailWord_1878257
  simp only [CollatzResearch.WordTrace]
  refine ⟨68505660756403144602049025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45670440504268763068032683 68505660756403144602049025)
  ·
    refine ⟨51379245567302358451536769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68505660756403144602049025 51379245567302358451536769)
    ·
      refine ⟨38534434175476768838652577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51379245567302358451536769 38534434175476768838652577)
      ·
        refine ⟨28900825631607576628989433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38534434175476768838652577 28900825631607576628989433)
        ·
          refine ⟨21675619223705682471742075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28900825631607576628989433 21675619223705682471742075)
          ·
            refine ⟨32513428835558523707613113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21675619223705682471742075 32513428835558523707613113)
            ·
              refine ⟨24385071626668892780709835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32513428835558523707613113 24385071626668892780709835)
              ·
                refine ⟨36577607440003339171064753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24385071626668892780709835 36577607440003339171064753)
                ·
                  refine ⟨27433205580002504378298565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36577607440003339171064753 27433205580002504378298565)
                  ·
                    refine ⟨5143726046250469570930981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27433205580002504378298565 5143726046250469570930981)
                    ·
                      refine ⟨964448633671963044549559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5143726046250469570930981 964448633671963044549559)
                      ·
                        rfl

theorem cell23_1878257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1878257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878257 prefixEnd_1878257 := by exact prefixLift 1878257
  have htrace : WordTrace (prefixWord ++ tailWord_1878257) baseStart_1878257 baseEnd_1878257 := by
    simpa [prefixWord, tailWord_1878257, baseEnd_1878257] using wordTrace_append hprefix tailTrace_1878257
  have hstable : (prefixWord ++ tailWord_1878257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878257).length < 2 ^ (prefixWord ++ tailWord_1878257).sum := by decide
  have hdescent : baseEnd_1878257 < baseStart_1878257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878271 : List Nat := [1, 1, 2, 2, 1, 4, 2, 5, 1, 4]
def baseStart_1878271 : Nat := 118140960795 + 1878271 * 2 ^ 59
def prefixEnd_1878271 : Nat := 4983230072969 + 3 ^ 40 * 1878271 * 2
def baseEnd_1878271 : Nat := 321485274133708663258165

theorem tailTrace_1878271 : CollatzResearch.WordTrace tailWord_1878271 prefixEnd_1878271 321485274133708663258165 := by
  unfold tailWord_1878271
  simp only [CollatzResearch.WordTrace]
  refine ⟨68506171378352424993058667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45670780918901616662039111 68506171378352424993058667)
  ·
    refine ⟨102759257067528637489588001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68506171378352424993058667 102759257067528637489588001)
    ·
      refine ⟨77069442800646478117191001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102759257067528637489588001 77069442800646478117191001)
      ·
        refine ⟨57802082100484858587893251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77069442800646478117191001 57802082100484858587893251)
        ·
          refine ⟨86703123150727287881839877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57802082100484858587893251 86703123150727287881839877)
          ·
            refine ⟨16256835590761366477844977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86703123150727287881839877 16256835590761366477844977)
            ·
              refine ⟨12192626693071024858383733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16256835590761366477844977 12192626693071024858383733)
              ·
                refine ⟨1143058752475408580473475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12192626693071024858383733 1143058752475408580473475)
                ·
                  refine ⟨1714588128713112870710213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143058752475408580473475 1714588128713112870710213)
                  ·
                    refine ⟨321485274133708663258165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714588128713112870710213 321485274133708663258165)
                    ·
                      rfl

theorem cell23_1878271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 5, 1, 4].length) (baseStart_1878271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878271 prefixEnd_1878271 := by exact prefixLift 1878271
  have htrace : WordTrace (prefixWord ++ tailWord_1878271) baseStart_1878271 baseEnd_1878271 := by
    simpa [prefixWord, tailWord_1878271, baseEnd_1878271] using wordTrace_append hprefix tailTrace_1878271
  have hstable : (prefixWord ++ tailWord_1878271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878271).length < 2 ^ (prefixWord ++ tailWord_1878271).sum := by decide
  have hdescent : baseEnd_1878271 < baseStart_1878271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878284 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 6]
def baseStart_1878284 : Nat := 118140960795 + 1878284 * 2 ^ 59
def prefixEnd_1878284 : Nat := 4983230072969 + 3 ^ 40 * 1878284 * 2
def baseEnd_1878284 : Nat := 107162499738848270990215

theorem tailTrace_1878284 : CollatzResearch.WordTrace tailWord_1878284 prefixEnd_1878284 107162499738848270990215 := by
  unfold tailWord_1878284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34253322763652664106640953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45671097018203552142187937 34253322763652664106640953)
  ·
    refine ⟨25689992072739498079980715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34253322763652664106640953 25689992072739498079980715)
    ·
      refine ⟨38534988109109247119971073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25689992072739498079980715 38534988109109247119971073)
      ·
        refine ⟨28901241081831935339978305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38534988109109247119971073 28901241081831935339978305)
        ·
          refine ⟨21675930811373951504983729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28901241081831935339978305 21675930811373951504983729)
          ·
            refine ⟨16256948108530463628737797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21675930811373951504983729 16256948108530463628737797)
            ·
              refine ⟨3048177770349461930388337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16256948108530463628737797 3048177770349461930388337)
              ·
                refine ⟨2286133327762096447791253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048177770349461930388337 2286133327762096447791253)
                ·
                  refine ⟨107162499738848270990215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2286133327762096447791253 107162499738848270990215)
                  ·
                    rfl

theorem cell23_1878284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 6].length) (baseStart_1878284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878284 prefixEnd_1878284 := by exact prefixLift 1878284
  have htrace : WordTrace (prefixWord ++ tailWord_1878284) baseStart_1878284 baseEnd_1878284 := by
    simpa [prefixWord, tailWord_1878284, baseEnd_1878284] using wordTrace_append hprefix tailTrace_1878284
  have hstable : (prefixWord ++ tailWord_1878284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878284).length < 2 ^ (prefixWord ++ tailWord_1878284).sum := by decide
  have hdescent : baseEnd_1878284 < baseStart_1878284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878307 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1878307 : Nat := 118140960795 + 1878307 * 2 ^ 59
def prefixEnd_1878307 : Nat := 4983230072969 + 3 ^ 40 * 1878307 * 2
def baseEnd_1878307 : Nat := 964474307704687848924329

theorem tailTrace_1878307 : CollatzResearch.WordTrace tailWord_1878307 prefixEnd_1878307 964474307704687848924329 := by
  unfold tailWord_1878307
  simp only [CollatzResearch.WordTrace]
  refine ⟨68507484406222003141369175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45671656270814668760912783 68507484406222003141369175)
  ·
    refine ⟨102761226609333004712053763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68507484406222003141369175 102761226609333004712053763)
    ·
      refine ⟨154141839913999507068080645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102761226609333004712053763 154141839913999507068080645)
      ·
        refine ⟨28901594983874907575265121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154141839913999507068080645 28901594983874907575265121)
        ·
          refine ⟨21676196237906180681448841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28901594983874907575265121 21676196237906180681448841)
          ·
            refine ⟨16257147178429635511086631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21676196237906180681448841 16257147178429635511086631)
            ·
              refine ⟨24385720767644453266629947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16257147178429635511086631 24385720767644453266629947)
              ·
                refine ⟨36578581151466679899944921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24385720767644453266629947 36578581151466679899944921)
                ·
                  refine ⟨27433935863600009924958691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36578581151466679899944921 27433935863600009924958691)
                  ·
                    refine ⟨41150903795400014887438037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27433935863600009924958691 41150903795400014887438037)
                    ·
                      refine ⟨964474307704687848924329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 41150903795400014887438037 964474307704687848924329)
                      ·
                        rfl

theorem cell23_1878307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1878307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878307 prefixEnd_1878307 := by exact prefixLift 1878307
  have htrace : WordTrace (prefixWord ++ tailWord_1878307) baseStart_1878307 baseEnd_1878307 := by
    simpa [prefixWord, tailWord_1878307, baseEnd_1878307] using wordTrace_append hprefix tailTrace_1878307
  have hstable : (prefixWord ++ tailWord_1878307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878307).length < 2 ^ (prefixWord ++ tailWord_1878307).sum := by decide
  have hdescent : baseEnd_1878307 < baseStart_1878307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878328 : List Nat := [2, 1, 2, 1, 3, 1, 3, 5, 1, 1, 3]
def baseStart_1878328 : Nat := 118140960795 + 1878328 * 2 ^ 59
def prefixEnd_1878328 : Nat := 4983230072969 + 3 ^ 40 * 1878328 * 2
def baseEnd_1878328 : Nat := 964485090798432266761733

theorem tailTrace_1878328 : CollatzResearch.WordTrace tailWord_1878328 prefixEnd_1878328 964485090798432266761733 := by
  unfold tailWord_1878328
  simp only [CollatzResearch.WordTrace]
  refine ⟨34254125169572961863941819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45672166892763949151922425 34254125169572961863941819)
  ·
    refine ⟨51381187754359442795912729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34254125169572961863941819 51381187754359442795912729)
    ·
      refine ⟨38535890815769582096934547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51381187754359442795912729 38535890815769582096934547)
      ·
        refine ⟨57803836223654373145401821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38535890815769582096934547 57803836223654373145401821)
        ·
          refine ⟨21676438583870389929525683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57803836223654373145401821 21676438583870389929525683)
          ·
            refine ⟨32514657875805584894288525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21676438583870389929525683 32514657875805584894288525)
            ·
              refine ⟨12192996703427094335358197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32514657875805584894288525 12192996703427094335358197)
              ·
                refine ⟨1143093440946290093939831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12192996703427094335358197 1143093440946290093939831)
                ·
                  refine ⟨1714640161419435140909747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143093440946290093939831 1714640161419435140909747)
                  ·
                    refine ⟨2571960242129152711364621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1714640161419435140909747 2571960242129152711364621)
                    ·
                      refine ⟨964485090798432266761733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2571960242129152711364621 964485090798432266761733)
                      ·
                        rfl

theorem cell23_1878328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_1878328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878328 prefixEnd_1878328 := by exact prefixLift 1878328
  have htrace : WordTrace (prefixWord ++ tailWord_1878328) baseStart_1878328 baseEnd_1878328 := by
    simpa [prefixWord, tailWord_1878328, baseEnd_1878328] using wordTrace_append hprefix tailTrace_1878328
  have hstable : (prefixWord ++ tailWord_1878328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878328).length < 2 ^ (prefixWord ++ tailWord_1878328).sum := by decide
  have hdescent : baseEnd_1878328 < baseStart_1878328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878354 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1878354 : Nat := 118140960795 + 1878354 * 2 ^ 59
def prefixEnd_1878354 : Nat := 4983230072969 + 3 ^ 40 * 1878354 * 2
def baseEnd_1878354 : Nat := 964498441295449165036613

theorem tailTrace_1878354 : CollatzResearch.WordTrace tailWord_1878354 prefixEnd_1878354 964498441295449165036613 := by
  unfold tailWord_1878354
  simp only [CollatzResearch.WordTrace]
  refine ⟨17127299659262932542082529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45672799091367820112220077 17127299659262932542082529)
  ·
    refine ⟨12845474744447199406561897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17127299659262932542082529 12845474744447199406561897)
    ·
      refine ⟨9634106058335399554921423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12845474744447199406561897 9634106058335399554921423)
      ·
        refine ⟨14451159087503099332382135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634106058335399554921423 14451159087503099332382135)
        ·
          refine ⟨21676738631254648998573203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14451159087503099332382135 21676738631254648998573203)
          ·
            refine ⟨32515107946881973497859805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21676738631254648998573203 32515107946881973497859805)
            ·
              refine ⟨12193165480080740061697427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32515107946881973497859805 12193165480080740061697427)
              ·
                refine ⟨18289748220121110092546141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193165480080740061697427 18289748220121110092546141)
                ·
                  refine ⟨6858655582545416284704803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18289748220121110092546141 6858655582545416284704803)
                  ·
                    refine ⟨10287983373818124427057205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6858655582545416284704803 10287983373818124427057205)
                    ·
                      refine ⟨964498441295449165036613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10287983373818124427057205 964498441295449165036613)
                      ·
                        rfl

theorem cell23_1878354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1878354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878354 prefixEnd_1878354 := by exact prefixLift 1878354
  have htrace : WordTrace (prefixWord ++ tailWord_1878354) baseStart_1878354 baseEnd_1878354 := by
    simpa [prefixWord, tailWord_1878354, baseEnd_1878354] using wordTrace_append hprefix tailTrace_1878354
  have hstable : (prefixWord ++ tailWord_1878354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878354).length < 2 ^ (prefixWord ++ tailWord_1878354).sum := by decide
  have hdescent : baseEnd_1878354 < baseStart_1878354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878368 : List Nat := [2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4]
def baseStart_1878368 : Nat := 118140960795 + 1878368 * 2 ^ 59
def prefixEnd_1878368 : Nat := 4983230072969 + 3 ^ 40 * 1878368 * 2
def baseEnd_1878368 : Nat := 964505630024612110261549

theorem tailTrace_1878368 : CollatzResearch.WordTrace tailWord_1878368 prefixEnd_1878368 964505630024612110261549 := by
  unfold tailWord_1878368
  simp only [CollatzResearch.WordTrace]
  refine ⟨34254854629500505279669879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45673139506000673706226505 34254854629500505279669879)
  ·
    refine ⟨51382281944250757919504819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34254854629500505279669879 51382281944250757919504819)
    ·
      refine ⟨77073422916376136879257229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51382281944250757919504819 77073422916376136879257229)
      ·
        refine ⟨28902533593641051329721461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77073422916376136879257229 28902533593641051329721461)
        ·
          refine ⟨2709612524403848562161387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28902533593641051329721461 2709612524403848562161387)
          ·
            refine ⟨4064418786605772843242081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709612524403848562161387 4064418786605772843242081)
            ·
              refine ⟨3048314089954329632431561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4064418786605772843242081 3048314089954329632431561)
              ·
                refine ⟨2286235567465747224323671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048314089954329632431561 2286235567465747224323671)
                ·
                  refine ⟨3429353351198620836485507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2286235567465747224323671 3429353351198620836485507)
                  ·
                    refine ⟨5144030026797931254728261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3429353351198620836485507 5144030026797931254728261)
                    ·
                      refine ⟨964505630024612110261549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5144030026797931254728261 964505630024612110261549)
                      ·
                        rfl

theorem cell23_1878368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 4].length) (baseStart_1878368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878368 prefixEnd_1878368 := by exact prefixLift 1878368
  have htrace : WordTrace (prefixWord ++ tailWord_1878368) baseStart_1878368 baseEnd_1878368 := by
    simpa [prefixWord, tailWord_1878368, baseEnd_1878368] using wordTrace_append hprefix tailTrace_1878368
  have hstable : (prefixWord ++ tailWord_1878368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878368).length < 2 ^ (prefixWord ++ tailWord_1878368).sum := by decide
  have hdescent : baseEnd_1878368 < baseStart_1878368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878404 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 2, 7]
def baseStart_1878404 : Nat := 118140960795 + 1878404 * 2 ^ 59
def prefixEnd_1878404 : Nat := 4983230072969 + 3 ^ 40 * 1878404 * 2
def baseEnd_1878404 : Nat := 321508038442724656470461

theorem tailTrace_1878404 : CollatzResearch.WordTrace tailWord_1878404 prefixEnd_1878404 321508038442724656470461 := by
  unfold tailWord_1878404
  simp only [CollatzResearch.WordTrace]
  refine ⟨34255511143435294353825133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45674014857913725805100177 34255511143435294353825133)
  ·
    refine ⟨12845816678788235382684425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34255511143435294353825133 12845816678788235382684425)
    ·
      refine ⟨9634362509091176537013319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12845816678788235382684425 9634362509091176537013319)
      ·
        refine ⟨14451543763636764805519979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9634362509091176537013319 14451543763636764805519979)
        ·
          refine ⟨21677315645455147208279969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14451543763636764805519979 21677315645455147208279969)
          ·
            refine ⟨16257986734091360406209977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21677315645455147208279969 16257986734091360406209977)
            ·
              refine ⟨12193490050568520304657483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16257986734091360406209977 12193490050568520304657483)
              ·
                refine ⟨18290235075852780456986225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193490050568520304657483 18290235075852780456986225)
                ·
                  refine ⟨13717676306889585342739669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290235075852780456986225 13717676306889585342739669)
                  ·
                    refine ⟨321508038442724656470461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13717676306889585342739669 321508038442724656470461)
                    ·
                      rfl

theorem cell23_1878404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_1878404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878404 prefixEnd_1878404 := by exact prefixLift 1878404
  have htrace : WordTrace (prefixWord ++ tailWord_1878404) baseStart_1878404 baseEnd_1878404 := by
    simpa [prefixWord, tailWord_1878404, baseEnd_1878404] using wordTrace_append hprefix tailTrace_1878404
  have hstable : (prefixWord ++ tailWord_1878404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878404).length < 2 ^ (prefixWord ++ tailWord_1878404).sum := by decide
  have hdescent : baseEnd_1878404 < baseStart_1878404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878458 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2]
def baseStart_1878458 : Nat := 118140960795 + 1878458 * 2 ^ 59
def prefixEnd_1878458 : Nat := 4983230072969 + 3 ^ 40 * 1878458 * 2
def baseEnd_1878458 : Nat := 964551843283516758136135

theorem tailTrace_1878458 : CollatzResearch.WordTrace tailWord_1878458 prefixEnd_1878458 964551843283516758136135 := by
  unfold tailWord_1878458
  simp only [CollatzResearch.WordTrace]
  refine ⟨17128247957168738982529007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45675327885783303953410685 17128247957168738982529007)
  ·
    refine ⟨25692371935753108473793511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17128247957168738982529007 25692371935753108473793511)
    ·
      refine ⟨38538557903629662710690267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25692371935753108473793511 38538557903629662710690267)
      ·
        refine ⟨57807836855444494066035401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38538557903629662710690267 57807836855444494066035401)
        ·
          refine ⟨43355877641583370549526551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57807836855444494066035401 43355877641583370549526551)
          ·
            refine ⟨65033816462375055824289827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43355877641583370549526551 65033816462375055824289827)
            ·
              refine ⟨97550724693562583736434741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65033816462375055824289827 97550724693562583736434741)
              ·
                refine ⟨9145380440021492225290757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97550724693562583736434741 9145380440021492225290757)
                ·
                  refine ⟨1714758832504029792242017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9145380440021492225290757 1714758832504029792242017)
                  ·
                    refine ⟨1286069124378022344181513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1714758832504029792242017 1286069124378022344181513)
                    ·
                      refine ⟨964551843283516758136135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286069124378022344181513 964551843283516758136135)
                      ·
                        rfl

theorem cell23_1878458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 2, 2].length) (baseStart_1878458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878458 prefixEnd_1878458 := by exact prefixLift 1878458
  have htrace : WordTrace (prefixWord ++ tailWord_1878458) baseStart_1878458 baseEnd_1878458 := by
    simpa [prefixWord, tailWord_1878458, baseEnd_1878458] using wordTrace_append hprefix tailTrace_1878458
  have hstable : (prefixWord ++ tailWord_1878458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878458).length < 2 ^ (prefixWord ++ tailWord_1878458).sum := by decide
  have hdescent : baseEnd_1878458 < baseStart_1878458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878461 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_1878461 : Nat := 118140960795 + 1878461 * 2 ^ 59
def prefixEnd_1878461 : Nat := 4983230072969 + 3 ^ 40 * 1878461 * 2
def baseEnd_1878461 : Nat := 964553383725480246398621

theorem tailTrace_1878461 : CollatzResearch.WordTrace tailWord_1878461 prefixEnd_1878461 964553383725480246398621 := by
  unfold tailWord_1878461
  simp only [CollatzResearch.WordTrace]
  refine ⟨68513101247664087442475237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45675400831776058294983491 68513101247664087442475237)
  ·
    refine ⟨12846206483937016395464107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68513101247664087442475237 12846206483937016395464107)
    ·
      refine ⟨19269309725905524593196161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12846206483937016395464107 19269309725905524593196161)
      ·
        refine ⟨14451982294429143444897121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19269309725905524593196161 14451982294429143444897121)
        ·
          refine ⟨10838986720821857583672841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14451982294429143444897121 10838986720821857583672841)
          ·
            refine ⟨8129240040616393187754631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10838986720821857583672841 8129240040616393187754631)
            ·
              refine ⟨12193860060924589781631947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8129240040616393187754631 12193860060924589781631947)
              ·
                refine ⟨18290790091386884672447921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12193860060924589781631947 18290790091386884672447921)
                ·
                  refine ⟨13718092568540163504335941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18290790091386884672447921 13718092568540163504335941)
                  ·
                    refine ⟨2572142356601280657062989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13718092568540163504335941 2572142356601280657062989)
                    ·
                      refine ⟨964553383725480246398621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2572142356601280657062989 964553383725480246398621)
                      ·
                        rfl

theorem cell23_1878461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_1878461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878461 prefixEnd_1878461 := by exact prefixLift 1878461
  have htrace : WordTrace (prefixWord ++ tailWord_1878461) baseStart_1878461 baseEnd_1878461 := by
    simpa [prefixWord, tailWord_1878461, baseEnd_1878461] using wordTrace_append hprefix tailTrace_1878461
  have hstable : (prefixWord ++ tailWord_1878461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878461).length < 2 ^ (prefixWord ++ tailWord_1878461).sum := by decide
  have hdescent : baseEnd_1878461 < baseStart_1878461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878464 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 7]
def baseStart_1878464 : Nat := 118140960795 + 1878464 * 2 ^ 59
def prefixEnd_1878464 : Nat := 4983230072969 + 3 ^ 40 * 1878464 * 2
def baseEnd_1878464 : Nat := 107172769351938192740123

theorem tailTrace_1878464 : CollatzResearch.WordTrace tailWord_1878464 prefixEnd_1878464 107172769351938192740123 := by
  unfold tailWord_1878464
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256605333326609477417223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45675473777768812636556297 34256605333326609477417223)
  ·
    refine ⟨51384907999989914216125835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34256605333326609477417223 51384907999989914216125835)
    ·
      refine ⟨77077361999984871324188753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51384907999989914216125835 77077361999984871324188753)
      ·
        refine ⟨57808021499988653493141565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77077361999984871324188753 57808021499988653493141565)
        ·
          refine ⟨21678008062495745059928087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57808021499988653493141565 21678008062495745059928087)
          ·
            refine ⟨32517012093743617589892131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21678008062495745059928087 32517012093743617589892131)
            ·
              refine ⟨48775518140615426384838197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32517012093743617589892131 48775518140615426384838197)
              ·
                refine ⟨4572704825682696223578581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48775518140615426384838197 4572704825682696223578581)
                ·
                  refine ⟨107172769351938192740123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4572704825682696223578581 107172769351938192740123)
                  ·
                    rfl

theorem cell23_1878464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 7].length) (baseStart_1878464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878464 prefixEnd_1878464 := by exact prefixLift 1878464
  have htrace : WordTrace (prefixWord ++ tailWord_1878464) baseStart_1878464 baseEnd_1878464 := by
    simpa [prefixWord, tailWord_1878464, baseEnd_1878464] using wordTrace_append hprefix tailTrace_1878464
  have hstable : (prefixWord ++ tailWord_1878464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878464).length < 2 ^ (prefixWord ++ tailWord_1878464).sum := by decide
  have hdescent : baseEnd_1878464 < baseStart_1878464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878468 : List Nat := [2, 3, 3, 2, 2, 1, 1, 1, 2, 6]
def baseStart_1878468 : Nat := 118140960795 + 1878468 * 2 ^ 59
def prefixEnd_1878468 : Nat := 4983230072969 + 3 ^ 40 * 1878468 * 2
def baseEnd_1878468 : Nat := 321518992696687239670363

theorem tailTrace_1878468 : CollatzResearch.WordTrace tailWord_1878468 prefixEnd_1878468 321518992696687239670363 := by
  unfold tailWord_1878468
  simp only [CollatzResearch.WordTrace]
  refine ⟨34256678279319363818990029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45675571039092485091986705 34256678279319363818990029)
  ·
    refine ⟨12846254354744761432121261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34256678279319363818990029 12846254354744761432121261)
    ·
      refine ⟨4817345383029285537045473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12846254354744761432121261 4817345383029285537045473)
      ·
        refine ⟨3613009037271964152784105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4817345383029285537045473 3613009037271964152784105)
        ·
          refine ⟨2709756777953973114588079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3613009037271964152784105 2709756777953973114588079)
          ·
            refine ⟨4064635166930959671882119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709756777953973114588079 4064635166930959671882119)
            ·
              refine ⟨6096952750396439507823179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064635166930959671882119 6096952750396439507823179)
              ·
                refine ⟨9145429125594659261734769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096952750396439507823179 9145429125594659261734769)
                ·
                  refine ⟨6859071844195994446301077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145429125594659261734769 6859071844195994446301077)
                  ·
                    refine ⟨321518992696687239670363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6859071844195994446301077 321518992696687239670363)
                    ·
                      rfl

theorem cell23_1878468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_1878468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878468 prefixEnd_1878468 := by exact prefixLift 1878468
  have htrace : WordTrace (prefixWord ++ tailWord_1878468) baseStart_1878468 baseEnd_1878468 := by
    simpa [prefixWord, tailWord_1878468, baseEnd_1878468] using wordTrace_append hprefix tailTrace_1878468
  have hstable : (prefixWord ++ tailWord_1878468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878468).length < 2 ^ (prefixWord ++ tailWord_1878468).sum := by decide
  have hdescent : baseEnd_1878468 < baseStart_1878468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878471 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1878471 : Nat := 118140960795 + 1878471 * 2 ^ 59
def prefixEnd_1878471 : Nat := 4983230072969 + 3 ^ 40 * 1878471 * 2
def baseEnd_1878471 : Nat := 964558518532025207273575

theorem tailTrace_1878471 : CollatzResearch.WordTrace tailWord_1878471 prefixEnd_1878471 964558518532025207273575 := by
  unfold tailWord_1878471
  simp only [CollatzResearch.WordTrace]
  refine ⟨68513465977627859150339267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45675643985085239433559511 68513465977627859150339267)
  ·
    refine ⟨102770198966441788725508901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68513465977627859150339267 102770198966441788725508901)
    ·
      refine ⟨19269412306207835386032919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102770198966441788725508901 19269412306207835386032919)
      ·
        refine ⟨28904118459311753079049379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19269412306207835386032919 28904118459311753079049379)
        ·
          refine ⟨43356177688967629618574069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28904118459311753079049379 43356177688967629618574069)
          ·
            refine ⟨4064641658340715276741319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43356177688967629618574069 4064641658340715276741319)
            ·
              refine ⟨6096962487511072915111979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064641658340715276741319 6096962487511072915111979)
              ·
                refine ⟨9145443731266609372667969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6096962487511072915111979 9145443731266609372667969)
                ·
                  refine ⟨6859082798449957029500977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9145443731266609372667969 6859082798449957029500977)
                  ·
                    refine ⟨5144312098837467772125733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859082798449957029500977 5144312098837467772125733)
                    ·
                      refine ⟨964558518532025207273575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5144312098837467772125733 964558518532025207273575)
                      ·
                        rfl

theorem cell23_1878471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1878471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878471 prefixEnd_1878471 := by exact prefixLift 1878471
  have htrace : WordTrace (prefixWord ++ tailWord_1878471) baseStart_1878471 baseEnd_1878471 := by
    simpa [prefixWord, tailWord_1878471, baseEnd_1878471] using wordTrace_append hprefix tailTrace_1878471
  have hstable : (prefixWord ++ tailWord_1878471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878471).length < 2 ^ (prefixWord ++ tailWord_1878471).sum := by decide
  have hdescent : baseEnd_1878471 < baseStart_1878471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878509 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 2, 2, 2]
def baseStart_1878509 : Nat := 118140960795 + 1878509 * 2 ^ 59
def prefixEnd_1878509 : Nat := 4983230072969 + 3 ^ 40 * 1878509 * 2
def baseEnd_1878509 : Nat := 964578030796896058598401

theorem tailTrace_1878509 : CollatzResearch.WordTrace tailWord_1878509 prefixEnd_1878509 964578030796896058598401 := by
  unfold tailWord_1878509
  simp only [CollatzResearch.WordTrace]
  refine ⟨68514851951490191640222581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45676567967660127760148387 68514851951490191640222581)
  ·
    refine ⟨6423267370452205466270867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68514851951490191640222581 6423267370452205466270867)
    ·
      refine ⟨9634901055678308199406301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6423267370452205466270867 9634901055678308199406301)
      ·
        refine ⟨3613087895879365574777363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9634901055678308199406301 3613087895879365574777363)
        ·
          refine ⟨5419631843819048362166045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613087895879365574777363 5419631843819048362166045)
          ·
            refine ⟨2032361941432143135812267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5419631843819048362166045 2032361941432143135812267)
            ·
              refine ⟨3048542912148214703718401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032361941432143135812267 3048542912148214703718401)
              ·
                refine ⟨2286407184111161027788801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3048542912148214703718401 2286407184111161027788801)
                ·
                  refine ⟨1714805388083370770841601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2286407184111161027788801 1714805388083370770841601)
                  ·
                    refine ⟨1286104041062528078131201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1714805388083370770841601 1286104041062528078131201)
                    ·
                      refine ⟨964578030796896058598401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286104041062528078131201 964578030796896058598401)
                      ·
                        rfl

theorem cell23_1878509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_1878509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878509 prefixEnd_1878509 := by exact prefixLift 1878509
  have htrace : WordTrace (prefixWord ++ tailWord_1878509) baseStart_1878509 baseEnd_1878509 := by
    simpa [prefixWord, tailWord_1878509, baseEnd_1878509] using wordTrace_append hprefix tailTrace_1878509
  have hstable : (prefixWord ++ tailWord_1878509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878509).length < 2 ^ (prefixWord ++ tailWord_1878509).sum := by decide
  have hdescent : baseEnd_1878509 < baseStart_1878509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878588 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 6]
def baseStart_1878588 : Nat := 118140960795 + 1878588 * 2 ^ 59
def prefixEnd_1878588 : Nat := 4983230072969 + 3 ^ 40 * 1878588 * 2
def baseEnd_1878588 : Nat := 107179843974289027723393

theorem tailTrace_1878588 : CollatzResearch.WordTrace tailWord_1878588 prefixEnd_1878588 107179843974289027723393 := by
  unfold tailWord_1878588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34258866659101994066174209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45678488878802658754898945 34258866659101994066174209)
  ·
    refine ⟨25694149994326495549630657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34258866659101994066174209 25694149994326495549630657)
    ·
      refine ⟨19270612495744871662222993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25694149994326495549630657 19270612495744871662222993)
      ·
        refine ⟨14452959371808653746667245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19270612495744871662222993 14452959371808653746667245)
        ·
          refine ⟨5419859764428245155000217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14452959371808653746667245 5419859764428245155000217)
          ·
            refine ⟨4064894823321183866250163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5419859764428245155000217 4064894823321183866250163)
            ·
              refine ⟨6097342234981775799375245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4064894823321183866250163 6097342234981775799375245)
              ·
                refine ⟨2286503338118165924765717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6097342234981775799375245 2286503338118165924765717)
                ·
                  refine ⟨107179843974289027723393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2286503338118165924765717 107179843974289027723393)
                  ·
                    rfl

theorem cell23_1878588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 6].length) (baseStart_1878588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878588 prefixEnd_1878588 := by exact prefixLift 1878588
  have htrace : WordTrace (prefixWord ++ tailWord_1878588) baseStart_1878588 baseEnd_1878588 := by
    simpa [prefixWord, tailWord_1878588, baseEnd_1878588] using wordTrace_append hprefix tailTrace_1878588
  have hstable : (prefixWord ++ tailWord_1878588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878588).length < 2 ^ (prefixWord ++ tailWord_1878588).sum := by decide
  have hdescent : baseEnd_1878588 < baseStart_1878588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878625 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 2, 3, 2]
def baseStart_1878625 : Nat := 118140960795 + 1878625 * 2 ^ 59
def prefixEnd_1878625 : Nat := 4983230072969 + 3 ^ 40 * 1878625 * 2
def baseEnd_1878625 : Nat := 964637594552817604747867

theorem tailTrace_1878625 : CollatzResearch.WordTrace tailWord_1878625 prefixEnd_1878625 964637594552817604747867 := by
  unfold tailWord_1878625
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519082819069943451445329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45679388546046628967630219 68519082819069943451445329)
  ·
    refine ⟨51389312114302457588583997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68519082819069943451445329 51389312114302457588583997)
    ·
      refine ⟨19270992042863421595718999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51389312114302457588583997 19270992042863421595718999)
      ·
        refine ⟨28906488064295132393578499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19270992042863421595718999 28906488064295132393578499)
        ·
          refine ⟨43359732096442698590367749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28906488064295132393578499 43359732096442698590367749)
          ·
            refine ⟨8129949768083005985693953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43359732096442698590367749 8129949768083005985693953)
            ·
              refine ⟨6097462326062254489270465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8129949768083005985693953 6097462326062254489270465)
              ·
                refine ⟨4573096744546690866952849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6097462326062254489270465 4573096744546690866952849)
                ·
                  refine ⟨3429822558410018150214637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573096744546690866952849 3429822558410018150214637)
                  ·
                    refine ⟨1286183459403756806330489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3429822558410018150214637 1286183459403756806330489)
                    ·
                      refine ⟨964637594552817604747867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286183459403756806330489 964637594552817604747867)
                      ·
                        rfl

theorem cell23_1878625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_1878625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878625 prefixEnd_1878625 := by exact prefixLift 1878625
  have htrace : WordTrace (prefixWord ++ tailWord_1878625) baseStart_1878625 baseEnd_1878625 := by
    simpa [prefixWord, tailWord_1878625, baseEnd_1878625] using wordTrace_append hprefix tailTrace_1878625
  have hstable : (prefixWord ++ tailWord_1878625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878625).length < 2 ^ (prefixWord ++ tailWord_1878625).sum := by decide
  have hdescent : baseEnd_1878625 < baseStart_1878625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878631 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 5, 6]
def baseStart_1878631 : Nat := 118140960795 + 1878631 * 2 ^ 59
def prefixEnd_1878631 : Nat := 4983230072969 + 3 ^ 40 * 1878631 * 2
def baseEnd_1878631 : Nat := 321546891812248193757613

theorem tailTrace_1878631 : CollatzResearch.WordTrace tailWord_1878631 prefixEnd_1878631 321546891812248193757613 := by
  unfold tailWord_1878631
  simp only [CollatzResearch.WordTrace]
  refine ⟨68519301657048206476163747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45679534438032137650775831 68519301657048206476163747)
  ·
    refine ⟨102778952485572309714245621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68519301657048206476163747 102778952485572309714245621)
    ·
      refine ⟨9635526795522404035710527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102778952485572309714245621 9635526795522404035710527)
      ·
        refine ⟨14453290193283606053565791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635526795522404035710527 14453290193283606053565791)
        ·
          refine ⟨21679935289925409080348687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14453290193283606053565791 21679935289925409080348687)
          ·
            refine ⟨32519902934888113620523031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21679935289925409080348687 32519902934888113620523031)
            ·
              refine ⟨48779854402332170430784547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32519902934888113620523031 48779854402332170430784547)
              ·
                refine ⟨73169781603498255646176821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48779854402332170430784547 73169781603498255646176821)
                ·
                  refine ⟨6859667025327961466829077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73169781603498255646176821 6859667025327961466829077)
                  ·
                    refine ⟨321546891812248193757613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6859667025327961466829077 321546891812248193757613)
                    ·
                      rfl

theorem cell23_1878631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_1878631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878631 prefixEnd_1878631 := by exact prefixLift 1878631
  have htrace : WordTrace (prefixWord ++ tailWord_1878631) baseStart_1878631 baseEnd_1878631 := by
    simpa [prefixWord, tailWord_1878631, baseEnd_1878631] using wordTrace_append hprefix tailTrace_1878631
  have hstable : (prefixWord ++ tailWord_1878631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878631).length < 2 ^ (prefixWord ++ tailWord_1878631).sum := by decide
  have hdescent : baseEnd_1878631 < baseStart_1878631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878682 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 4, 4]
def baseStart_1878682 : Nat := 118140960795 + 1878682 * 2 ^ 59
def prefixEnd_1878682 : Nat := 4983230072969 + 3 ^ 40 * 1878682 * 2
def baseEnd_1878682 : Nat := 321555620983374627245035

theorem tailTrace_1878682 : CollatzResearch.WordTrace tailWord_1878682 prefixEnd_1878682 321555620983374627245035 := by
  unfold tailWord_1878682
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130290444965860546567575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45680774519908961457513533 17130290444965860546567575)
  ·
    refine ⟨25695435667448790819851363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17130290444965860546567575 25695435667448790819851363)
    ·
      refine ⟨38543153501173186229777045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25695435667448790819851363 38543153501173186229777045)
      ·
        refine ⟨1806710320367493104520799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38543153501173186229777045 1806710320367493104520799)
        ·
          refine ⟨2710065480551239656781199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806710320367493104520799 2710065480551239656781199)
          ·
            refine ⟨4065098220826859485171799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710065480551239656781199 4065098220826859485171799)
            ·
              refine ⟨6097647331240289227757699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065098220826859485171799 6097647331240289227757699)
              ·
                refine ⟨9146470996860433841636549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6097647331240289227757699 9146470996860433841636549)
                ·
                  refine ⟨1714963311911331345306853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9146470996860433841636549 1714963311911331345306853)
                  ·
                    refine ⟨321555620983374627245035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1714963311911331345306853 321555620983374627245035)
                    ·
                      rfl

theorem cell23_1878682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 4, 4].length) (baseStart_1878682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878682 prefixEnd_1878682 := by exact prefixLift 1878682
  have htrace : WordTrace (prefixWord ++ tailWord_1878682) baseStart_1878682 baseEnd_1878682 := by
    simpa [prefixWord, tailWord_1878682, baseEnd_1878682] using wordTrace_append hprefix tailTrace_1878682
  have hstable : (prefixWord ++ tailWord_1878682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878682).length < 2 ^ (prefixWord ++ tailWord_1878682).sum := by decide
  have hdescent : baseEnd_1878682 < baseStart_1878682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878689 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 3, 2, 2]
def baseStart_1878689 : Nat := 118140960795 + 1878689 * 2 ^ 59
def prefixEnd_1878689 : Nat := 4983230072969 + 3 ^ 40 * 1878689 * 2
def baseEnd_1878689 : Nat := 964670457314705354347573

theorem tailTrace_1878689 : CollatzResearch.WordTrace tailWord_1878689 prefixEnd_1878689 964670457314705354347573 := by
  unfold tailWord_1878689
  simp only [CollatzResearch.WordTrace]
  refine ⟨68521417090838082381775121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45680944727225388254516747 68521417090838082381775121)
  ·
    refine ⟨51391062818128561786331341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68521417090838082381775121 51391062818128561786331341)
    ·
      refine ⟨19271648556798210669874253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51391062818128561786331341 19271648556798210669874253)
      ·
        refine ⟨7226868208799329001202845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19271648556798210669874253 7226868208799329001202845)
        ·
          refine ⟨2710075578299748375451067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7226868208799329001202845 2710075578299748375451067)
          ·
            refine ⟨4065113367449622563176601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710075578299748375451067 4065113367449622563176601)
            ·
              refine ⟨3048835025587216922382451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065113367449622563176601 3048835025587216922382451)
              ·
                refine ⟨4573252538380825383573677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048835025587216922382451 4573252538380825383573677)
                ·
                  refine ⟨1714969701892809518840129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4573252538380825383573677 1714969701892809518840129)
                  ·
                    refine ⟨1286227276419607139130097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1714969701892809518840129 1286227276419607139130097)
                    ·
                      refine ⟨964670457314705354347573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286227276419607139130097 964670457314705354347573)
                      ·
                        rfl

theorem cell23_1878689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_1878689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878689 prefixEnd_1878689 := by exact prefixLift 1878689
  have htrace : WordTrace (prefixWord ++ tailWord_1878689) baseStart_1878689 baseEnd_1878689 := by
    simpa [prefixWord, tailWord_1878689, baseEnd_1878689] using wordTrace_append hprefix tailTrace_1878689
  have hstable : (prefixWord ++ tailWord_1878689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878689).length < 2 ^ (prefixWord ++ tailWord_1878689).sum := by decide
  have hdescent : baseEnd_1878689 < baseStart_1878689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878691 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 2, 7]
def baseStart_1878691 : Nat := 118140960795 + 1878691 * 2 ^ 59
def prefixEnd_1878691 : Nat := 4983230072969 + 3 ^ 40 * 1878691 * 2
def baseEnd_1878691 : Nat := 321557161425338115507521

theorem tailTrace_1878691 : CollatzResearch.WordTrace tailWord_1878691 prefixEnd_1878691 321557161425338115507521 := by
  unfold tailWord_1878691
  simp only [CollatzResearch.WordTrace]
  refine ⟨68521490036830836723347927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45680993357887224482231951 68521490036830836723347927)
  ·
    refine ⟨102782235055246255085021891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68521490036830836723347927 102782235055246255085021891)
    ·
      refine ⟨154173352582869382627532837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102782235055246255085021891 154173352582869382627532837)
      ·
        refine ⟨28907503609288009242662407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154173352582869382627532837 28907503609288009242662407)
        ·
          refine ⟨43361255413932013863993611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28907503609288009242662407 43361255413932013863993611)
          ·
            refine ⟨65041883120898020795990417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43361255413932013863993611 65041883120898020795990417)
            ·
              refine ⟨48781412340673515596992813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65041883120898020795990417 48781412340673515596992813)
              ·
                refine ⟨18293029627752568348872305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48781412340673515596992813 18293029627752568348872305)
                ·
                  refine ⟨13719772220814426261654229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18293029627752568348872305 13719772220814426261654229)
                  ·
                    refine ⟨321557161425338115507521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13719772220814426261654229 321557161425338115507521)
                    ·
                      rfl

theorem cell23_1878691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 7].length) (baseStart_1878691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878691 prefixEnd_1878691 := by exact prefixLift 1878691
  have htrace : WordTrace (prefixWord ++ tailWord_1878691) baseStart_1878691 baseEnd_1878691 := by
    simpa [prefixWord, tailWord_1878691, baseEnd_1878691] using wordTrace_append hprefix tailTrace_1878691
  have hstable : (prefixWord ++ tailWord_1878691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878691).length < 2 ^ (prefixWord ++ tailWord_1878691).sum := by decide
  have hdescent : baseEnd_1878691 < baseStart_1878691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878702 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1878702 : Nat := 118140960795 + 1878702 * 2 ^ 59
def prefixEnd_1878702 : Nat := 4983230072969 + 3 ^ 40 * 1878702 * 2
def baseEnd_1878702 : Nat := 964677132563213803485013

theorem tailTrace_1878702 : CollatzResearch.WordTrace tailWord_1878702 prefixEnd_1878702 964677132563213803485013 := by
  unfold tailWord_1878702
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565236404973873200249795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45681260826527323734665573 8565236404973873200249795)
  ·
    refine ⟨12847854607460809800374693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8565236404973873200249795 12847854607460809800374693)
    ·
      refine ⟨2408972738898901837570255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12847854607460809800374693 2408972738898901837570255)
      ·
        refine ⟨3613459108348352756355383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408972738898901837570255 3613459108348352756355383)
        ·
          refine ⟨5420188662522529134533075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3613459108348352756355383 5420188662522529134533075)
          ·
            refine ⟨8130282993783793701799613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420188662522529134533075 8130282993783793701799613)
            ·
              refine ⟨3048856122668922638174855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8130282993783793701799613 3048856122668922638174855)
              ·
                refine ⟨4573284184003383957262283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3048856122668922638174855 4573284184003383957262283)
                ·
                  refine ⟨6859926276005075935893425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573284184003383957262283 6859926276005075935893425)
                  ·
                    refine ⟨5144944707003806951920069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6859926276005075935893425 5144944707003806951920069)
                    ·
                      refine ⟨964677132563213803485013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5144944707003806951920069 964677132563213803485013)
                      ·
                        rfl

theorem cell23_1878702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1878702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878702 prefixEnd_1878702 := by exact prefixLift 1878702
  have htrace : WordTrace (prefixWord ++ tailWord_1878702) baseStart_1878702 baseEnd_1878702 := by
    simpa [prefixWord, tailWord_1878702, baseEnd_1878702] using wordTrace_append hprefix tailTrace_1878702
  have hstable : (prefixWord ++ tailWord_1878702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878702).length < 2 ^ (prefixWord ++ tailWord_1878702).sum := by decide
  have hdescent : baseEnd_1878702 < baseStart_1878702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878718 : List Nat := [4, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1878718 : Nat := 118140960795 + 1878718 * 2 ^ 59
def prefixEnd_1878718 : Nat := 4983230072969 + 3 ^ 40 * 1878718 * 2
def baseEnd_1878718 : Nat := 964685348253685740884939

theorem tailTrace_1878718 : CollatzResearch.WordTrace tailWord_1878718 prefixEnd_1878718 964685348253685740884939 := by
  unfold tailWord_1878718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565309350966627541822601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45681649871822013556387205 8565309350966627541822601)
  ·
    refine ⟨6423982013224970656366951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8565309350966627541822601 6423982013224970656366951)
    ·
      refine ⟨9635973019837455984550427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6423982013224970656366951 9635973019837455984550427)
      ·
        refine ⟨14453959529756183976825641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9635973019837455984550427 14453959529756183976825641)
        ·
          refine ⟨10840469647317137982619231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14453959529756183976825641 10840469647317137982619231)
          ·
            refine ⟨16260704470975706973928847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10840469647317137982619231 16260704470975706973928847)
            ·
              refine ⟨24391056706463560460893271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16260704470975706973928847 24391056706463560460893271)
              ·
                refine ⟨36586585059695340691339907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24391056706463560460893271 36586585059695340691339907)
                ·
                  refine ⟨54879877589543011037009861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36586585059695340691339907 54879877589543011037009861)
                  ·
                    refine ⟨10289977048039314569439349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54879877589543011037009861 10289977048039314569439349)
                    ·
                      refine ⟨964685348253685740884939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10289977048039314569439349 964685348253685740884939)
                      ·
                        rfl

theorem cell23_1878718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1878718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878718 prefixEnd_1878718 := by exact prefixLift 1878718
  have htrace : WordTrace (prefixWord ++ tailWord_1878718) baseStart_1878718 baseEnd_1878718 := by
    simpa [prefixWord, tailWord_1878718, baseEnd_1878718] using wordTrace_append hprefix tailTrace_1878718
  have hstable : (prefixWord ++ tailWord_1878718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878718).length < 2 ^ (prefixWord ++ tailWord_1878718).sum := by decide
  have hdescent : baseEnd_1878718 < baseStart_1878718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878785 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 5]
def baseStart_1878785 : Nat := 118140960795 + 1878785 * 2 ^ 59
def prefixEnd_1878785 : Nat := 4983230072969 + 3 ^ 40 * 1878785 * 2
def baseEnd_1878785 : Nat := 107191083495281886527459

theorem tailTrace_1878785 : CollatzResearch.WordTrace tailWord_1878785 prefixEnd_1878785 107191083495281886527459 := by
  unfold tailWord_1878785
  simp only [CollatzResearch.WordTrace]
  refine ⟨68524918498490290777269809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45683278998993527184846539 68524918498490290777269809)
  ·
    refine ⟨51393688873867718082952357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68524918498490290777269809 51393688873867718082952357)
    ·
      refine ⟨9636316663850197140553567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51393688873867718082952357 9636316663850197140553567)
      ·
        refine ⟨14454474995775295710830351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9636316663850197140553567 14454474995775295710830351)
        ·
          refine ⟨21681712493662943566245527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454474995775295710830351 21681712493662943566245527)
          ·
            refine ⟨32522568740494415349368291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681712493662943566245527 32522568740494415349368291)
            ·
              refine ⟨48783853110741623024052437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32522568740494415349368291 48783853110741623024052437)
              ·
                refine ⟨1143371557283006789626229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48783853110741623024052437 1143371557283006789626229)
                ·
                  refine ⟨107191083495281886527459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1143371557283006789626229 107191083495281886527459)
                  ·
                    rfl

theorem cell23_1878785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 5].length) (baseStart_1878785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878785 prefixEnd_1878785 := by exact prefixLift 1878785
  have htrace : WordTrace (prefixWord ++ tailWord_1878785) baseStart_1878785 baseEnd_1878785 := by
    simpa [prefixWord, tailWord_1878785, baseEnd_1878785] using wordTrace_append hprefix tailTrace_1878785
  have hstable : (prefixWord ++ tailWord_1878785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878785).length < 2 ^ (prefixWord ++ tailWord_1878785).sum := by decide
  have hdescent : baseEnd_1878785 < baseStart_1878785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878798 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 3, 7]
def baseStart_1878798 : Nat := 118140960795 + 1878798 * 2 ^ 59
def prefixEnd_1878798 : Nat := 4983230072969 + 3 ^ 40 * 1878798 * 2
def baseEnd_1878798 : Nat := 321575475568681809294857

theorem tailTrace_1878798 : CollatzResearch.WordTrace tailWord_1878798 prefixEnd_1878798 321575475568681809294857 := by
  unfold tailWord_1878798
  simp only [CollatzResearch.WordTrace]
  refine ⟨8565674080930399249686631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45683595098295462664995365 8565674080930399249686631)
  ·
    refine ⟨12848511121395598874529947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8565674080930399249686631 12848511121395598874529947)
    ·
      refine ⟨19272766682093398311794921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848511121395598874529947 19272766682093398311794921)
      ·
        refine ⟨14454575011570048733846191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19272766682093398311794921 14454575011570048733846191)
        ·
          refine ⟨21681862517355073100769287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14454575011570048733846191 21681862517355073100769287)
          ·
            refine ⟨32522793776032609651153931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21681862517355073100769287 32522793776032609651153931)
            ·
              refine ⟨48784190664048914476730897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32522793776032609651153931 48784190664048914476730897)
              ·
                refine ⟨36588142998036685857548173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48784190664048914476730897 36588142998036685857548173)
                ·
                  refine ⟨13720553624263757196580565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36588142998036685857548173 13720553624263757196580565)
                  ·
                    refine ⟨321575475568681809294857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13720553624263757196580565 321575475568681809294857)
                    ·
                      rfl

theorem cell23_1878798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_1878798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878798 prefixEnd_1878798 := by exact prefixLift 1878798
  have htrace : WordTrace (prefixWord ++ tailWord_1878798) baseStart_1878798 baseEnd_1878798 := by
    simpa [prefixWord, tailWord_1878798, baseEnd_1878798] using wordTrace_append hprefix tailTrace_1878798
  have hstable : (prefixWord ++ tailWord_1878798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878798).length < 2 ^ (prefixWord ++ tailWord_1878798).sum := by decide
  have hdescent : baseEnd_1878798 < baseStart_1878798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878805 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_1878805 : Nat := 118140960795 + 1878805 * 2 ^ 59
def prefixEnd_1878805 : Nat := 4983230072969 + 3 ^ 40 * 1878805 * 2
def baseEnd_1878805 : Nat := 964730021070626900497039

theorem tailTrace_1878805 : CollatzResearch.WordTrace tailWord_1878805 prefixEnd_1878805 964730021070626900497039 := by
  unfold tailWord_1878805
  simp only [CollatzResearch.WordTrace]
  refine ⟨68525647958417834192997869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45683765305611889461998579 68525647958417834192997869)
  ·
    refine ⟨25697117984406687822374201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68525647958417834192997869 25697117984406687822374201)
    ·
      refine ⟨19272838488305015866780651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25697117984406687822374201 19272838488305015866780651)
      ·
        refine ⟨28909257732457523800170977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272838488305015866780651 28909257732457523800170977)
        ·
          refine ⟨21681943299343142850128233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28909257732457523800170977 21681943299343142850128233)
          ·
            refine ⟨16261457474507357137596175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21681943299343142850128233 16261457474507357137596175)
            ·
              refine ⟨24392186211761035706394263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16261457474507357137596175 24392186211761035706394263)
              ·
                refine ⟨36588279317641553559591395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24392186211761035706394263 36588279317641553559591395)
                ·
                  refine ⟨54882418976462330339387093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36588279317641553559591395 54882418976462330339387093)
                  ·
                    refine ⟨1286306694760835867329385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54882418976462330339387093 1286306694760835867329385)
                    ·
                      refine ⟨964730021070626900497039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286306694760835867329385 964730021070626900497039)
                      ·
                        rfl

theorem cell23_1878805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_1878805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878805 prefixEnd_1878805 := by exact prefixLift 1878805
  have htrace : WordTrace (prefixWord ++ tailWord_1878805) baseStart_1878805 baseEnd_1878805 := by
    simpa [prefixWord, tailWord_1878805, baseEnd_1878805] using wordTrace_append hprefix tailTrace_1878805
  have hstable : (prefixWord ++ tailWord_1878805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878805).length < 2 ^ (prefixWord ++ tailWord_1878805).sum := by decide
  have hdescent : baseEnd_1878805 < baseStart_1878805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878835 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4]
def baseStart_1878835 : Nat := 118140960795 + 1878835 * 2 ^ 59
def prefixEnd_1878835 : Nat := 4983230072969 + 3 ^ 40 * 1878835 * 2
def baseEnd_1878835 : Nat := 964745425490261783121901

theorem tailTrace_1878835 : CollatzResearch.WordTrace tailWord_1878835 prefixEnd_1878835 964745425490261783121901 := by
  unfold tailWord_1878835
  simp only [CollatzResearch.WordTrace]
  refine ⟨68526742148309149316589959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45684494765539432877726639 68526742148309149316589959)
  ·
    refine ⟨102790113222463723974884939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68526742148309149316589959 102790113222463723974884939)
    ·
      refine ⟨154185169833695585962327409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102790113222463723974884939 154185169833695585962327409)
      ·
        refine ⟨115638877375271689471745557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154185169833695585962327409 115638877375271689471745557)
        ·
          refine ⟨5420572376965860443988073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115638877375271689471745557 5420572376965860443988073)
          ·
            refine ⟨4065429282724395332991055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420572376965860443988073 4065429282724395332991055)
            ·
              refine ⟨6098143924086592999486583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065429282724395332991055 6098143924086592999486583)
              ·
                refine ⟨9147215886129889499229875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6098143924086592999486583 9147215886129889499229875)
                ·
                  refine ⟨13720823829194834248844813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9147215886129889499229875 13720823829194834248844813)
                  ·
                    refine ⟨5145308935948062843316805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13720823829194834248844813 5145308935948062843316805)
                    ·
                      refine ⟨964745425490261783121901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5145308935948062843316805 964745425490261783121901)
                      ·
                        rfl

theorem cell23_1878835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 3, 4].length) (baseStart_1878835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878835 prefixEnd_1878835 := by exact prefixLift 1878835
  have htrace : WordTrace (prefixWord ++ tailWord_1878835) baseStart_1878835 baseEnd_1878835 := by
    simpa [prefixWord, tailWord_1878835, baseEnd_1878835] using wordTrace_append hprefix tailTrace_1878835
  have hstable : (prefixWord ++ tailWord_1878835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878835).length < 2 ^ (prefixWord ++ tailWord_1878835).sum := by decide
  have hdescent : baseEnd_1878835 < baseStart_1878835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878848 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1878848 : Nat := 118140960795 + 1878848 * 2 ^ 59
def prefixEnd_1878848 : Nat := 4983230072969 + 3 ^ 40 * 1878848 * 2
def baseEnd_1878848 : Nat := 964752100738770232259341

theorem tailTrace_1878848 : CollatzResearch.WordTrace tailWord_1878848 prefixEnd_1878848 964752100738770232259341 := by
  unfold tailWord_1878848
  simp only [CollatzResearch.WordTrace]
  refine ⟨34263608148631026268406599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45684810864841368357875465 34263608148631026268406599)
  ·
    refine ⟨51395412222946539402609899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34263608148631026268406599 51395412222946539402609899)
    ·
      refine ⟨77093118334419809103914849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51395412222946539402609899 77093118334419809103914849)
      ·
        refine ⟨57819838750814856827936137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77093118334419809103914849 57819838750814856827936137)
        ·
          refine ⟨43364879063111142620952103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57819838750814856827936137 43364879063111142620952103)
          ·
            refine ⟨65047318594666713931428155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43364879063111142620952103 65047318594666713931428155)
            ·
              refine ⟨97570977892000070897142233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65047318594666713931428155 97570977892000070897142233)
              ·
                refine ⟨73178233419000053172856675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97570977892000070897142233 73178233419000053172856675)
                ·
                  refine ⟨109767350128500079759285013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73178233419000053172856675 109767350128500079759285013)
                  ·
                    refine ⟨5145344537273441238716485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 109767350128500079759285013 5145344537273441238716485)
                    ·
                      refine ⟨964752100738770232259341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5145344537273441238716485 964752100738770232259341)
                      ·
                        rfl

theorem cell23_1878848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1878848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878848 prefixEnd_1878848 := by exact prefixLift 1878848
  have htrace : WordTrace (prefixWord ++ tailWord_1878848) baseStart_1878848 baseEnd_1878848 := by
    simpa [prefixWord, tailWord_1878848, baseEnd_1878848] using wordTrace_append hprefix tailTrace_1878848
  have hstable : (prefixWord ++ tailWord_1878848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878848).length < 2 ^ (prefixWord ++ tailWord_1878848).sum := by decide
  have hdescent : baseEnd_1878848 < baseStart_1878848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878855 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_1878855 : Nat := 118140960795 + 1878855 * 2 ^ 59
def prefixEnd_1878855 : Nat := 4983230072969 + 3 ^ 40 * 1878855 * 2
def baseEnd_1878855 : Nat := 964755695103351704871809

theorem tailTrace_1878855 : CollatzResearch.WordTrace tailWord_1878855 prefixEnd_1878855 964755695103351704871809 := by
  unfold tailWord_1878855
  simp only [CollatzResearch.WordTrace]
  refine ⟨68527471608236692732318019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45684981072157795154878679 68527471608236692732318019)
  ·
    refine ⟨102791207412355039098477029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68527471608236692732318019 102791207412355039098477029)
    ·
      refine ⟨19273351389816569830964443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102791207412355039098477029 19273351389816569830964443)
      ·
        refine ⟨28910027084724854746446665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19273351389816569830964443 28910027084724854746446665)
        ·
          refine ⟨21682520313543641059834999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28910027084724854746446665 21682520313543641059834999)
          ·
            refine ⟨32523780470315461589752499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21682520313543641059834999 32523780470315461589752499)
            ·
              refine ⟨48785670705473192384628749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32523780470315461589752499 48785670705473192384628749)
              ·
                refine ⟨18294626514552447144235781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48785670705473192384628749 18294626514552447144235781)
                ·
                  refine ⟨3430242471478583839544209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18294626514552447144235781 3430242471478583839544209)
                  ·
                    refine ⟨2572681853608937879658157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430242471478583839544209 2572681853608937879658157)
                    ·
                      refine ⟨964755695103351704871809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2572681853608937879658157 964755695103351704871809)
                      ·
                        rfl

theorem cell23_1878855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_1878855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878855 prefixEnd_1878855 := by exact prefixLift 1878855
  have htrace : WordTrace (prefixWord ++ tailWord_1878855) baseStart_1878855 baseEnd_1878855 := by
    simpa [prefixWord, tailWord_1878855, baseEnd_1878855] using wordTrace_append hprefix tailTrace_1878855
  have hstable : (prefixWord ++ tailWord_1878855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878855).length < 2 ^ (prefixWord ++ tailWord_1878855).sum := by decide
  have hdescent : baseEnd_1878855 < baseStart_1878855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878919 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_1878919 : Nat := 118140960795 + 1878919 * 2 ^ 59
def prefixEnd_1878919 : Nat := 4983230072969 + 3 ^ 40 * 1878919 * 2
def baseEnd_1878919 : Nat := 964788557865239454471515

theorem tailTrace_1878919 : CollatzResearch.WordTrace tailWord_1878919 prefixEnd_1878919 964788557865239454471515 := by
  unfold tailWord_1878919
  simp only [CollatzResearch.WordTrace]
  refine ⟨68529805880004831662647811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45686537253336554441765207 68529805880004831662647811)
  ·
    refine ⟨102794708820007247493971717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68529805880004831662647811 102794708820007247493971717)
    ·
      refine ⟨19274007903751358905119697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102794708820007247493971717 19274007903751358905119697)
      ·
        refine ⟨14455505927813519178839773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19274007903751358905119697 14455505927813519178839773)
        ·
          refine ⟨5420814722930069692064915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14455505927813519178839773 5420814722930069692064915)
          ·
            refine ⟨8131222084395104538097373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5420814722930069692064915 8131222084395104538097373)
            ·
              refine ⟨3049208281648164201786515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8131222084395104538097373 3049208281648164201786515)
              ·
                refine ⟨4573812422472246302679773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049208281648164201786515 4573812422472246302679773)
                ·
                  refine ⟨1715179658427092363504915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4573812422472246302679773 1715179658427092363504915)
                  ·
                    refine ⟨2572769487640638545257373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715179658427092363504915 2572769487640638545257373)
                    ·
                      refine ⟨964788557865239454471515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2572769487640638545257373 964788557865239454471515)
                      ·
                        rfl

theorem cell23_1878919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_1878919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878919 prefixEnd_1878919 := by exact prefixLift 1878919
  have htrace : WordTrace (prefixWord ++ tailWord_1878919) baseStart_1878919 baseEnd_1878919 := by
    simpa [prefixWord, tailWord_1878919, baseEnd_1878919] using wordTrace_append hprefix tailTrace_1878919
  have hstable : (prefixWord ++ tailWord_1878919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878919).length < 2 ^ (prefixWord ++ tailWord_1878919).sum := by decide
  have hdescent : baseEnd_1878919 < baseStart_1878919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878935 : List Nat := [1, 1, 3, 3, 1, 2, 2, 3, 1, 6]
def baseStart_1878935 : Nat := 118140960795 + 1878935 * 2 ^ 59
def prefixEnd_1878935 : Nat := 4983230072969 + 3 ^ 40 * 1878935 * 2
def baseEnd_1878935 : Nat := 321598924518570463957147

theorem tailTrace_1878935 : CollatzResearch.WordTrace tailWord_1878935 prefixEnd_1878935 321598924518570463957147 := by
  unfold tailWord_1878935
  simp only [CollatzResearch.WordTrace]
  refine ⟨68530389447946866395230259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45686926298631244263486839 68530389447946866395230259)
  ·
    refine ⟨102795584171920299592845389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68530389447946866395230259 102795584171920299592845389)
    ·
      refine ⟨38548344064470112347317021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102795584171920299592845389 38548344064470112347317021)
      ·
        refine ⟨14455629024176292130243883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38548344064470112347317021 14455629024176292130243883)
        ·
          refine ⟨21683443536264438195365825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14455629024176292130243883 21683443536264438195365825)
          ·
            refine ⟨16262582652198328646524369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21683443536264438195365825 16262582652198328646524369)
            ·
              refine ⟨12196936989148746484893277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16262582652198328646524369 12196936989148746484893277)
              ·
                refine ⟨4573851370930779931834979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12196936989148746484893277 4573851370930779931834979)
                ·
                  refine ⟨6860777056396169897752469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573851370930779931834979 6860777056396169897752469)
                  ·
                    refine ⟨321598924518570463957147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6860777056396169897752469 321598924518570463957147)
                    ·
                      rfl

theorem cell23_1878935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 6].length) (baseStart_1878935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878935 prefixEnd_1878935 := by exact prefixLift 1878935
  have htrace : WordTrace (prefixWord ++ tailWord_1878935) baseStart_1878935 baseEnd_1878935 := by
    simpa [prefixWord, tailWord_1878935, baseEnd_1878935] using wordTrace_append hprefix tailTrace_1878935
  have hstable : (prefixWord ++ tailWord_1878935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878935).length < 2 ^ (prefixWord ++ tailWord_1878935).sum := by decide
  have hdescent : baseEnd_1878935 < baseStart_1878935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878946 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1878946 : Nat := 118140960795 + 1878946 * 2 ^ 59
def prefixEnd_1878946 : Nat := 4983230072969 + 3 ^ 40 * 1878946 * 2
def baseEnd_1878946 : Nat := 964802421842910848833891

theorem tailTrace_1878946 : CollatzResearch.WordTrace tailWord_1878946 prefixEnd_1878946 964802421842910848833891 := by
  unfold tailWord_1878946
  simp only [CollatzResearch.WordTrace]
  refine ⟨17132697662726753818470173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45687193767271343515920461 17132697662726753818470173)
  ·
    refine ⟨6424761623522532681926315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17132697662726753818470173 6424761623522532681926315)
    ·
      refine ⟨9637142435283799022889473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6424761623522532681926315 9637142435283799022889473)
      ·
        refine ⟨7227856826462849267167105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9637142435283799022889473 7227856826462849267167105)
        ·
          refine ⟨5420892619847136950375329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7227856826462849267167105 5420892619847136950375329)
          ·
            refine ⟨4065669464885352712781497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5420892619847136950375329 4065669464885352712781497)
            ·
              refine ⟨3049252098664014534586123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065669464885352712781497 3049252098664014534586123)
              ·
                refine ⟨4573878147996021801879185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049252098664014534586123 4573878147996021801879185)
                ·
                  refine ⟨3430408610997016351409389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4573878147996021801879185 3430408610997016351409389)
                  ·
                    refine ⟨1286403229123881131778521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3430408610997016351409389 1286403229123881131778521)
                    ·
                      refine ⟨964802421842910848833891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286403229123881131778521 964802421842910848833891)
                      ·
                        rfl

theorem cell23_1878946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1878946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878946 prefixEnd_1878946 := by exact prefixLift 1878946
  have htrace : WordTrace (prefixWord ++ tailWord_1878946) baseStart_1878946 baseEnd_1878946 := by
    simpa [prefixWord, tailWord_1878946, baseEnd_1878946] using wordTrace_append hprefix tailTrace_1878946
  have hstable : (prefixWord ++ tailWord_1878946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878946).length < 2 ^ (prefixWord ++ tailWord_1878946).sum := by decide
  have hdescent : baseEnd_1878946 < baseStart_1878946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878955 : List Nat := [1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4]
def baseStart_1878955 : Nat := 118140960795 + 1878955 * 2 ^ 59
def prefixEnd_1878955 : Nat := 4983230072969 + 3 ^ 40 * 1878955 * 2
def baseEnd_1878955 : Nat := 964807043168801313621349

theorem tailTrace_1878955 : CollatzResearch.WordTrace tailWord_1878955 prefixEnd_1878955 964807043168801313621349 := by
  unfold tailWord_1878955
  simp only [CollatzResearch.WordTrace]
  refine ⟨68531118907874409810958319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45687412605249606540638879 68531118907874409810958319)
  ·
    refine ⟨102796678361811614716437479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68531118907874409810958319 102796678361811614716437479)
    ·
      refine ⟨154195017542717422074656219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102796678361811614716437479 154195017542717422074656219)
      ·
        refine ⟨231292526314076133111984329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154195017542717422074656219 231292526314076133111984329)
        ·
          refine ⟨173469394735557099833988247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231292526314076133111984329 173469394735557099833988247)
          ·
            refine ⟨260204092103335649750982371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173469394735557099833988247 260204092103335649750982371)
            ·
              refine ⟨390306138155003474626473557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260204092103335649750982371 390306138155003474626473557)
              ·
                refine ⟨4573900056503946968278987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 390306138155003474626473557 4573900056503946968278987)
                ·
                  refine ⟨6860850084755920452418481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4573900056503946968278987 6860850084755920452418481)
                  ·
                    refine ⟨5145637563566940339313861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6860850084755920452418481 5145637563566940339313861)
                    ·
                      refine ⟨964807043168801313621349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5145637563566940339313861 964807043168801313621349)
                      ·
                        rfl

theorem cell23_1878955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 2, 4].length) (baseStart_1878955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878955 prefixEnd_1878955 := by exact prefixLift 1878955
  have htrace : WordTrace (prefixWord ++ tailWord_1878955) baseStart_1878955 baseEnd_1878955 := by
    simpa [prefixWord, tailWord_1878955, baseEnd_1878955] using wordTrace_append hprefix tailTrace_1878955
  have hstable : (prefixWord ++ tailWord_1878955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878955).length < 2 ^ (prefixWord ++ tailWord_1878955).sum := by decide
  have hdescent : baseEnd_1878955 < baseStart_1878955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878969 : List Nat := [1, 2, 1, 4, 2, 3, 2, 2, 2, 4]
def baseStart_1878969 : Nat := 118140960795 + 1878969 * 2 ^ 59
def prefixEnd_1878969 : Nat := 4983230072969 + 3 ^ 40 * 1878969 * 2
def baseEnd_1878969 : Nat := 321604743965988086282095

theorem tailTrace_1878969 : CollatzResearch.WordTrace tailWord_1878969 prefixEnd_1878969 321604743965988086282095 := by
  unfold tailWord_1878969
  simp only [CollatzResearch.WordTrace]
  refine ⟨68531629529823690201967961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45687753019882460134645307 68531629529823690201967961)
  ·
    refine ⟨51398722147367767651475971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68531629529823690201967961 51398722147367767651475971)
    ·
      refine ⟨77098083221051651477213957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51398722147367767651475971 77098083221051651477213957)
      ·
        refine ⟨14455890603947184651977617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77098083221051651477213957 14455890603947184651977617)
        ·
          refine ⟨10841917952960388488983213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14455890603947184651977617 10841917952960388488983213)
          ·
            refine ⟨4065719232360145683368705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10841917952960388488983213 4065719232360145683368705)
            ·
              refine ⟨3049289424270109262526529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4065719232360145683368705 3049289424270109262526529)
              ·
                refine ⟨2286967068202581946894897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049289424270109262526529 2286967068202581946894897)
                ·
                  refine ⟨1715225301151936460171173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2286967068202581946894897 1715225301151936460171173)
                  ·
                    refine ⟨321604743965988086282095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1715225301151936460171173 321604743965988086282095)
                    ·
                      rfl

theorem cell23_1878969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 2, 4].length) (baseStart_1878969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878969 prefixEnd_1878969 := by exact prefixLift 1878969
  have htrace : WordTrace (prefixWord ++ tailWord_1878969) baseStart_1878969 baseEnd_1878969 := by
    simpa [prefixWord, tailWord_1878969, baseEnd_1878969] using wordTrace_append hprefix tailTrace_1878969
  have hstable : (prefixWord ++ tailWord_1878969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878969).length < 2 ^ (prefixWord ++ tailWord_1878969).sum := by decide
  have hdescent : baseEnd_1878969 < baseStart_1878969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1878992 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3]
def baseStart_1878992 : Nat := 118140960795 + 1878992 * 2 ^ 59
def prefixEnd_1878992 : Nat := 4983230072969 + 3 ^ 40 * 1878992 * 2
def baseEnd_1878992 : Nat := 964826041953017668858679

theorem tailTrace_1878992 : CollatzResearch.WordTrace tailWord_1878992 prefixEnd_1878992 964826041953017668858679 := by
  unfold tailWord_1878992
  simp only [CollatzResearch.WordTrace]
  refine ⟨34266234204370182565027615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45688312272493576753370153 34266234204370182565027615)
  ·
    refine ⟨51399351306555273847541423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34266234204370182565027615 51399351306555273847541423)
    ·
      refine ⟨77099026959832910771312135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51399351306555273847541423 77099026959832910771312135)
      ·
        refine ⟨115648540439749366156968203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77099026959832910771312135 115648540439749366156968203)
        ·
          refine ⟨173472810659624049235452305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115648540439749366156968203 173472810659624049235452305)
          ·
            refine ⟨130104607994718036926589229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173472810659624049235452305 130104607994718036926589229)
            ·
              refine ⟨48789227998019263847470961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130104607994718036926589229 48789227998019263847470961)
              ·
                refine ⟨36591920998514447885603221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48789227998019263847470961 36591920998514447885603221)
                ·
                  refine ⟨1715246296805364744637651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 36591920998514447885603221 1715246296805364744637651)
                  ·
                    refine ⟨2572869445208047116956477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715246296805364744637651 2572869445208047116956477)
                    ·
                      refine ⟨964826041953017668858679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2572869445208047116956477 964826041953017668858679)
                      ·
                        rfl

theorem cell23_1878992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 6, 1, 3].length) (baseStart_1878992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1878992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1878992 prefixEnd_1878992 := by exact prefixLift 1878992
  have htrace : WordTrace (prefixWord ++ tailWord_1878992) baseStart_1878992 baseEnd_1878992 := by
    simpa [prefixWord, tailWord_1878992, baseEnd_1878992] using wordTrace_append hprefix tailTrace_1878992
  have hstable : (prefixWord ++ tailWord_1878992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1878992).length < 2 ^ (prefixWord ++ tailWord_1878992).sum := by decide
  have hdescent : baseEnd_1878992 < baseStart_1878992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1878992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879010 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_1879010 : Nat := 118140960795 + 1879010 * 2 ^ 59
def prefixEnd_1879010 : Nat := 4983230072969 + 3 ^ 40 * 1879010 * 2
def baseEnd_1879010 : Nat := 964835284604798598433597

theorem tailTrace_1879010 : CollatzResearch.WordTrace tailWord_1879010 prefixEnd_1879010 964835284604798598433597 := by
  unfold tailWord_1879010
  simp only [CollatzResearch.WordTrace]
  refine ⟨17133281230668788551052621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45688749948450102802806989 17133281230668788551052621)
  ·
    refine ⟨6424980461500795706644733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17133281230668788551052621 6424980461500795706644733)
    ·
      refine ⟨2409367673062798389991775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6424980461500795706644733 2409367673062798389991775)
      ·
        refine ⟨3614051509594197584987663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409367673062798389991775 3614051509594197584987663)
        ·
          refine ⟨5421077264391296377481495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614051509594197584987663 5421077264391296377481495)
          ·
            refine ⟨8131615896586944566222243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421077264391296377481495 8131615896586944566222243)
            ·
              refine ⟨12197423844880416849333365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8131615896586944566222243 12197423844880416849333365)
              ·
                refine ⟨1143508485457539079625003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12197423844880416849333365 1143508485457539079625003)
                ·
                  refine ⟨1715262728186308619437505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143508485457539079625003 1715262728186308619437505)
                  ·
                    refine ⟨1286447046139731464578129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715262728186308619437505 1286447046139731464578129)
                    ·
                      refine ⟨964835284604798598433597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286447046139731464578129 964835284604798598433597)
                      ·
                        rfl

theorem cell23_1879010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_1879010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879010 prefixEnd_1879010 := by exact prefixLift 1879010
  have htrace : WordTrace (prefixWord ++ tailWord_1879010) baseStart_1879010 baseEnd_1879010 := by
    simpa [prefixWord, tailWord_1879010, baseEnd_1879010] using wordTrace_append hprefix tailTrace_1879010
  have hstable : (prefixWord ++ tailWord_1879010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879010).length < 2 ^ (prefixWord ++ tailWord_1879010).sum := by decide
  have hdescent : baseEnd_1879010 < baseStart_1879010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879035 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5]
def baseStart_1879035 : Nat := 118140960795 + 1879035 * 2 ^ 59
def prefixEnd_1879035 : Nat := 4983230072969 + 3 ^ 40 * 1879035 * 2
def baseEnd_1879035 : Nat := 964848121621161000620981

theorem tailTrace_1879035 : CollatzResearch.WordTrace tailWord_1879035 prefixEnd_1879035 964848121621161000620981 := by
  unfold tailWord_1879035
  simp only [CollatzResearch.WordTrace]
  refine ⟨68534036747584583473870559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45689357831723055649247039 68534036747584583473870559)
  ·
    refine ⟨102801055121376875210805839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68534036747584583473870559 102801055121376875210805839)
    ·
      refine ⟨154201582682065312816208759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102801055121376875210805839 154201582682065312816208759)
      ·
        refine ⟨231302374023097969224313139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154201582682065312816208759 231302374023097969224313139)
        ·
          refine ⟨346953561034646953836469709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231302374023097969224313139 346953561034646953836469709)
          ·
            refine ⟨130107585387992607688676141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 346953561034646953836469709 130107585387992607688676141)
            ·
              refine ⟨48790344520497227883253553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130107585387992607688676141 48790344520497227883253553)
              ·
                refine ⟨36592758390372920912440165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48790344520497227883253553 36592758390372920912440165)
                ·
                  refine ⟨6861142198194922671082531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36592758390372920912440165 6861142198194922671082531)
                  ·
                    refine ⟨10291713297292384006623797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861142198194922671082531 10291713297292384006623797)
                    ·
                      refine ⟨964848121621161000620981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10291713297292384006623797 964848121621161000620981)
                      ·
                        rfl

theorem cell23_1879035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 5].length) (baseStart_1879035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879035 prefixEnd_1879035 := by exact prefixLift 1879035
  have htrace : WordTrace (prefixWord ++ tailWord_1879035) baseStart_1879035 baseEnd_1879035 := by
    simpa [prefixWord, tailWord_1879035, baseEnd_1879035] using wordTrace_append hprefix tailTrace_1879035
  have hstable : (prefixWord ++ tailWord_1879035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879035).length < 2 ^ (prefixWord ++ tailWord_1879035).sum := by decide
  have hdescent : baseEnd_1879035 < baseStart_1879035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879069 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_1879069 : Nat := 118140960795 + 1879069 * 2 ^ 59
def prefixEnd_1879069 : Nat := 4983230072969 + 3 ^ 40 * 1879069 * 2
def baseEnd_1879069 : Nat := 964865579963413867595825

theorem tailTrace_1879069 : CollatzResearch.WordTrace tailWord_1879069 prefixEnd_1879069 964865579963413867595825 := by
  unfold tailWord_1879069
  simp only [CollatzResearch.WordTrace]
  refine ⟨68535276829461407280608261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45690184552974271520405507 68535276829461407280608261)
  ·
    refine ⟨12850364405524013865114049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68535276829461407280608261 12850364405524013865114049)
    ·
      refine ⟨9637773304143010398835537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12850364405524013865114049 9637773304143010398835537)
      ·
        refine ⟨7228329978107257799126653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9637773304143010398835537 7228329978107257799126653)
        ·
          refine ⟨2710623741790221674672495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7228329978107257799126653 2710623741790221674672495)
          ·
            refine ⟨4065935612685332512008743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710623741790221674672495 4065935612685332512008743)
            ·
              refine ⟨6098903419027998768013115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4065935612685332512008743 6098903419027998768013115)
              ·
                refine ⟨9148355128541998152019673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6098903419027998768013115 9148355128541998152019673)
                ·
                  refine ⟨6861266346406498614014755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148355128541998152019673 6861266346406498614014755)
                  ·
                    refine ⟨10291899519609747921022133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6861266346406498614014755 10291899519609747921022133)
                    ·
                      refine ⟨964865579963413867595825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10291899519609747921022133 964865579963413867595825)
                      ·
                        rfl

theorem cell23_1879069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_1879069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879069 prefixEnd_1879069 := by exact prefixLift 1879069
  have htrace : WordTrace (prefixWord ++ tailWord_1879069) baseStart_1879069 baseEnd_1879069 := by
    simpa [prefixWord, tailWord_1879069, baseEnd_1879069] using wordTrace_append hprefix tailTrace_1879069
  have hstable : (prefixWord ++ tailWord_1879069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879069).length < 2 ^ (prefixWord ++ tailWord_1879069).sum := by decide
  have hdescent : baseEnd_1879069 < baseStart_1879069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879100 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_1879100 : Nat := 118140960795 + 1879100 * 2 ^ 59
def prefixEnd_1879100 : Nat := 4983230072969 + 3 ^ 40 * 1879100 * 2
def baseEnd_1879100 : Nat := 964881497863703246308183

theorem tailTrace_1879100 : CollatzResearch.WordTrace tailWord_1879100 prefixEnd_1879100 964881497863703246308183 := by
  unfold tailWord_1879100
  simp only [CollatzResearch.WordTrace]
  refine ⟨34268203746174549787493377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45690938328232733049991169 34268203746174549787493377)
  ·
    refine ⟨25701152809630912340620033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34268203746174549787493377 25701152809630912340620033)
    ·
      refine ⟨19275864607223184255465025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25701152809630912340620033 19275864607223184255465025)
      ·
        refine ⟨14456898455417388191598769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19275864607223184255465025 14456898455417388191598769)
        ·
          refine ⟨10842673841563041143699077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14456898455417388191598769 10842673841563041143699077)
          ·
            refine ⟨2033001345293070214443577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10842673841563041143699077 2033001345293070214443577)
            ·
              refine ⟨1524751008969802660832683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033001345293070214443577 1524751008969802660832683)
              ·
                refine ⟨2287126513454703991249025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524751008969802660832683 2287126513454703991249025)
                ·
                  refine ⟨1715344885091027993436769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287126513454703991249025 1715344885091027993436769)
                  ·
                    refine ⟨1286508663818270995077577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715344885091027993436769 1286508663818270995077577)
                    ·
                      refine ⟨964881497863703246308183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286508663818270995077577 964881497863703246308183)
                      ·
                        rfl

theorem cell23_1879100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_1879100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879100 prefixEnd_1879100 := by exact prefixLift 1879100
  have htrace : WordTrace (prefixWord ++ tailWord_1879100) baseStart_1879100 baseEnd_1879100 := by
    simpa [prefixWord, tailWord_1879100, baseEnd_1879100] using wordTrace_append hprefix tailTrace_1879100
  have hstable : (prefixWord ++ tailWord_1879100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879100).length < 2 ^ (prefixWord ++ tailWord_1879100).sum := by decide
  have hdescent : baseEnd_1879100 < baseStart_1879100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879139 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1879139 : Nat := 118140960795 + 1879139 * 2 ^ 59
def prefixEnd_1879139 : Nat := 4983230072969 + 3 ^ 40 * 1879139 * 2
def baseEnd_1879139 : Nat := 964901523609228593720503

theorem tailTrace_1879139 : CollatzResearch.WordTrace tailWord_1879139 prefixEnd_1879139 964901523609228593720503 := by
  unfold tailWord_1879139
  simp only [CollatzResearch.WordTrace]
  refine ⟨68537829939207809235656471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45691886626138539490437647 68537829939207809235656471)
  ·
    refine ⟨102806744908811713853484707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68537829939207809235656471 102806744908811713853484707)
    ·
      refine ⟨154210117363217570780227061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102806744908811713853484707 154210117363217570780227061)
      ·
        refine ⟨14457198502801647260646287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154210117363217570780227061 14457198502801647260646287)
        ·
          refine ⟨21685797754202470890969431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457198502801647260646287 21685797754202470890969431)
          ·
            refine ⟨32528696631303706336454147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21685797754202470890969431 32528696631303706336454147)
            ·
              refine ⟨48793044946955559504681221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32528696631303706336454147 48793044946955559504681221)
              ·
                refine ⟨9148695927554167407127729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48793044946955559504681221 9148695927554167407127729)
                ·
                  refine ⟨6861521945665625555345797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9148695927554167407127729 6861521945665625555345797)
                  ·
                    refine ⟨1286535364812304791627337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6861521945665625555345797 1286535364812304791627337)
                    ·
                      refine ⟨964901523609228593720503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286535364812304791627337 964901523609228593720503)
                      ·
                        rfl

theorem cell23_1879139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1879139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879139 prefixEnd_1879139 := by exact prefixLift 1879139
  have htrace : WordTrace (prefixWord ++ tailWord_1879139) baseStart_1879139 baseEnd_1879139 := by
    simpa [prefixWord, tailWord_1879139, baseEnd_1879139] using wordTrace_append hprefix tailTrace_1879139
  have hstable : (prefixWord ++ tailWord_1879139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879139).length < 2 ^ (prefixWord ++ tailWord_1879139).sum := by decide
  have hdescent : baseEnd_1879139 < baseStart_1879139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879173 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_1879173 : Nat := 118140960795 + 1879173 * 2 ^ 59
def prefixEnd_1879173 : Nat := 4983230072969 + 3 ^ 40 * 1879173 * 2
def baseEnd_1879173 : Nat := 964918981951481460695347

theorem tailTrace_1879173 : CollatzResearch.WordTrace tailWord_1879173 prefixEnd_1879173 964918981951481460695347 := by
  unfold tailWord_1879173
  simp only [CollatzResearch.WordTrace]
  refine ⟨68539070021084633042394173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45692713347389755361596115 68539070021084633042394173)
  ·
    refine ⟨25702151257906737390897815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68539070021084633042394173 25702151257906737390897815)
    ·
      refine ⟨38553226886860106086346723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25702151257906737390897815 38553226886860106086346723)
      ·
        refine ⟨57829840330290159129520085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38553226886860106086346723 57829840330290159129520085)
        ·
          refine ⟨1355386882741175604598127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57829840330290159129520085 1355386882741175604598127)
          ·
            refine ⟨2033080324111763406897191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355386882741175604598127 2033080324111763406897191)
            ·
              refine ⟨3049620486167645110345787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033080324111763406897191 3049620486167645110345787)
              ·
                refine ⟨4574430729251467665518681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049620486167645110345787 4574430729251467665518681)
                ·
                  refine ⟨3430823046938600749139011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574430729251467665518681 3430823046938600749139011)
                  ·
                    refine ⟨5146234570407901123708517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430823046938600749139011 5146234570407901123708517)
                    ·
                      refine ⟨964918981951481460695347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5146234570407901123708517 964918981951481460695347)
                      ·
                        rfl

theorem cell23_1879173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_1879173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879173 prefixEnd_1879173 := by exact prefixLift 1879173
  have htrace : WordTrace (prefixWord ++ tailWord_1879173) baseStart_1879173 baseEnd_1879173 := by
    simpa [prefixWord, tailWord_1879173, baseEnd_1879173] using wordTrace_append hprefix tailTrace_1879173
  have hstable : (prefixWord ++ tailWord_1879173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879173).length < 2 ^ (prefixWord ++ tailWord_1879173).sum := by decide
  have hdescent : baseEnd_1879173 < baseStart_1879173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879176 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1879176 : Nat := 118140960795 + 1879176 * 2 ^ 59
def prefixEnd_1879176 : Nat := 4983230072969 + 3 ^ 40 * 1879176 * 2
def baseEnd_1879176 : Nat := 964920522393444948957833

theorem tailTrace_1879176 : CollatzResearch.WordTrace tailWord_1879176 prefixEnd_1879176 964920522393444948957833 := by
  unfold tailWord_1879176
  simp only [CollatzResearch.WordTrace]
  refine ⟨34269589720036882277376691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45692786293382509703168921 34269589720036882277376691)
  ·
    refine ⟨51404384580055323416065037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34269589720036882277376691 51404384580055323416065037)
    ·
      refine ⟨19276644217520746281024389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51404384580055323416065037 19276644217520746281024389)
      ·
        refine ⟨3614370790785139927692073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19276644217520746281024389 3614370790785139927692073)
        ·
          refine ⟨2710778093088854945769055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614370790785139927692073 2710778093088854945769055)
          ·
            refine ⟨4066167139633282418653583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710778093088854945769055 4066167139633282418653583)
            ·
              refine ⟨6099250709449923627980375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066167139633282418653583 6099250709449923627980375)
              ·
                refine ⟨9148876064174885441970563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099250709449923627980375 9148876064174885441970563)
                ·
                  refine ⟨13723314096262328162955845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9148876064174885441970563 13723314096262328162955845)
                  ·
                    refine ⟨2573121393049186530554221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13723314096262328162955845 2573121393049186530554221)
                    ·
                      refine ⟨964920522393444948957833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573121393049186530554221 964920522393444948957833)
                      ·
                        rfl

theorem cell23_1879176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1879176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879176 prefixEnd_1879176 := by exact prefixLift 1879176
  have htrace : WordTrace (prefixWord ++ tailWord_1879176) baseStart_1879176 baseEnd_1879176 := by
    simpa [prefixWord, tailWord_1879176, baseEnd_1879176] using wordTrace_append hprefix tailTrace_1879176
  have hstable : (prefixWord ++ tailWord_1879176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879176).length < 2 ^ (prefixWord ++ tailWord_1879176).sum := by decide
  have hdescent : baseEnd_1879176 < baseStart_1879176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879196 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 6]
def baseStart_1879196 : Nat := 118140960795 + 1879196 * 2 ^ 59
def prefixEnd_1879196 : Nat := 4983230072969 + 3 ^ 40 * 1879196 * 2
def baseEnd_1879196 : Nat := 107214532445170541189749

theorem tailTrace_1879196 : CollatzResearch.WordTrace tailWord_1879196 prefixEnd_1879196 107214532445170541189749 := by
  unfold tailWord_1879196
  simp only [CollatzResearch.WordTrace]
  refine ⟨34269954450000653985240721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45693272600000871980320961 34269954450000653985240721)
  ·
    refine ⟨25702465837500490488930541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34269954450000653985240721 25702465837500490488930541)
    ·
      refine ⟨9638424689062683933348953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25702465837500490488930541 9638424689062683933348953)
      ·
        refine ⟨7228818516797012950011715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9638424689062683933348953 7228818516797012950011715)
        ·
          refine ⟨10843227775195519425017573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7228818516797012950011715 10843227775195519425017573)
          ·
            refine ⟨2033105207849159892190795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10843227775195519425017573 2033105207849159892190795)
            ·
              refine ⟨3049657811773739838286193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033105207849159892190795 3049657811773739838286193)
              ·
                refine ⟨2287243358830304878714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049657811773739838286193 2287243358830304878714645)
                ·
                  refine ⟨107214532445170541189749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2287243358830304878714645 107214532445170541189749)
                  ·
                    rfl

theorem cell23_1879196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 6].length) (baseStart_1879196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879196 prefixEnd_1879196 := by exact prefixLift 1879196
  have htrace : WordTrace (prefixWord ++ tailWord_1879196) baseStart_1879196 baseEnd_1879196 := by
    simpa [prefixWord, tailWord_1879196, baseEnd_1879196] using wordTrace_append hprefix tailTrace_1879196
  have hstable : (prefixWord ++ tailWord_1879196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879196).length < 2 ^ (prefixWord ++ tailWord_1879196).sum := by decide
  have hdescent : baseEnd_1879196 < baseStart_1879196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879212 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 4]
def baseStart_1879212 : Nat := 118140960795 + 1879212 * 2 ^ 59
def prefixEnd_1879212 : Nat := 4983230072969 + 3 ^ 40 * 1879212 * 2
def baseEnd_1879212 : Nat := 964939007697006808107667

theorem tailTrace_1879212 : CollatzResearch.WordTrace tailWord_1879212 prefixEnd_1879212 964939007697006808107667 := by
  unfold tailWord_1879212
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270246233971671351531945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45693661645295561802042593 34270246233971671351531945)
  ·
    refine ⟨25702684675478753513648959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34270246233971671351531945 25702684675478753513648959)
    ·
      refine ⟨38554027013218130270473439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25702684675478753513648959 38554027013218130270473439)
      ·
        refine ⟨57831040519827195405710159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38554027013218130270473439 57831040519827195405710159)
        ·
          refine ⟨86746560779740793108565239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57831040519827195405710159 86746560779740793108565239)
          ·
            refine ⟨130119841169611189662847859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86746560779740793108565239 130119841169611189662847859)
            ·
              refine ⟨195179761754416784494271789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130119841169611189662847859 195179761754416784494271789)
              ·
                refine ⟨73192410657906294185351921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195179761754416784494271789 73192410657906294185351921)
                ·
                  refine ⟨54894307993429720639013941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73192410657906294185351921 54894307993429720639013941)
                  ·
                    refine ⟨5146341374384036309907557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54894307993429720639013941 5146341374384036309907557)
                    ·
                      refine ⟨964939007697006808107667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5146341374384036309907557 964939007697006808107667)
                      ·
                        rfl

theorem cell23_1879212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 4].length) (baseStart_1879212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879212 prefixEnd_1879212 := by exact prefixLift 1879212
  have htrace : WordTrace (prefixWord ++ tailWord_1879212) baseStart_1879212 baseEnd_1879212 := by
    simpa [prefixWord, tailWord_1879212, baseEnd_1879212] using wordTrace_append hprefix tailTrace_1879212
  have hstable : (prefixWord ++ tailWord_1879212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879212).length < 2 ^ (prefixWord ++ tailWord_1879212).sum := by decide
  have hdescent : baseEnd_1879212 < baseStart_1879212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879213 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 6]
def baseStart_1879213 : Nat := 118140960795 + 1879213 * 2 ^ 59
def prefixEnd_1879213 : Nat := 4983230072969 + 3 ^ 40 * 1879213 * 2
def baseEnd_1879213 : Nat := 107215502353073478243907

theorem tailTrace_1879213 : CollatzResearch.WordTrace tailWord_1879213 prefixEnd_1879213 107215502353073478243907 := by
  unfold tailWord_1879213
  simp only [CollatzResearch.WordTrace]
  refine ⟨68540528940939719873850293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45693685960626479915900195 68540528940939719873850293)
  ·
    refine ⟨6425674588213098738173465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68540528940939719873850293 6425674588213098738173465)
    ·
      refine ⟨4819255941159824053630099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6425674588213098738173465 4819255941159824053630099)
      ·
        refine ⟨7228883911739736080445149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4819255941159824053630099 7228883911739736080445149)
        ·
          refine ⟨2710831466902401030166931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7228883911739736080445149 2710831466902401030166931)
          ·
            refine ⟨4066247200353601545250397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710831466902401030166931 4066247200353601545250397)
            ·
              refine ⟨1524842700132600579468899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066247200353601545250397 1524842700132600579468899)
              ·
                refine ⟨2287264050198900869203349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524842700132600579468899 2287264050198900869203349)
                ·
                  refine ⟨107215502353073478243907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2287264050198900869203349 107215502353073478243907)
                  ·
                    rfl

theorem cell23_1879213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_1879213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879213 prefixEnd_1879213 := by exact prefixLift 1879213
  have htrace : WordTrace (prefixWord ++ tailWord_1879213) baseStart_1879213 baseEnd_1879213 := by
    simpa [prefixWord, tailWord_1879213, baseEnd_1879213] using wordTrace_append hprefix tailTrace_1879213
  have hstable : (prefixWord ++ tailWord_1879213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879213).length < 2 ^ (prefixWord ++ tailWord_1879213).sum := by decide
  have hdescent : baseEnd_1879213 < baseStart_1879213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879229 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_1879229 : Nat := 118140960795 + 1879229 * 2 ^ 59
def prefixEnd_1879229 : Nat := 4983230072969 + 3 ^ 40 * 1879229 * 2
def baseEnd_1879229 : Nat := 964947736868133241595089

theorem tailTrace_1879229 : CollatzResearch.WordTrace tailWord_1879229 prefixEnd_1879229 964947736868133241595089 := by
  unfold tailWord_1879229
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541112508881754606432741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45694075005921169737621827 68541112508881754606432741)
  ·
    refine ⟨12851458595415328988706139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68541112508881754606432741 12851458595415328988706139)
    ·
      refine ⟨19277187893122993483059209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851458595415328988706139 19277187893122993483059209)
      ·
        refine ⟨14457890919842245112294407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19277187893122993483059209 14457890919842245112294407)
        ·
          refine ⟨21686836379763367668441611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14457890919842245112294407 21686836379763367668441611)
          ·
            refine ⟨32530254569645051502662417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21686836379763367668441611 32530254569645051502662417)
            ·
              refine ⟨24397690927233788626996813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32530254569645051502662417 24397690927233788626996813)
              ·
                refine ⟨9149134097712670735123805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24397690927233788626996813 9149134097712670735123805)
                ·
                  refine ⟨3430925286642251525671427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9149134097712670735123805 3430925286642251525671427)
                  ·
                    refine ⟨5146387929963377288507141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3430925286642251525671427 5146387929963377288507141)
                    ·
                      refine ⟨964947736868133241595089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5146387929963377288507141 964947736868133241595089)
                      ·
                        rfl

theorem cell23_1879229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_1879229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879229 prefixEnd_1879229 := by exact prefixLift 1879229
  have htrace : WordTrace (prefixWord ++ tailWord_1879229) baseStart_1879229 baseEnd_1879229 := by
    simpa [prefixWord, tailWord_1879229, baseEnd_1879229] using wordTrace_append hprefix tailTrace_1879229
  have hstable : (prefixWord ++ tailWord_1879229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879229).length < 2 ^ (prefixWord ++ tailWord_1879229).sum := by decide
  have hdescent : baseEnd_1879229 < baseStart_1879229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879233 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_1879233 : Nat := 118140960795 + 1879233 * 2 ^ 59
def prefixEnd_1879233 : Nat := 4983230072969 + 3 ^ 40 * 1879233 * 2
def baseEnd_1879233 : Nat := 964949790790751225945071

theorem tailTrace_1879233 : CollatzResearch.WordTrace tailWord_1879233 prefixEnd_1879233 964949790790751225945071 := by
  unfold tailWord_1879233
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541258400867263289578353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45694172267244842193052235 68541258400867263289578353)
  ·
    refine ⟨51405943800650447467183765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68541258400867263289578353 51405943800650447467183765)
    ·
      refine ⟨2409653615655489725024239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51405943800650447467183765 2409653615655489725024239)
      ·
        refine ⟨3614480423483234587536359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409653615655489725024239 3614480423483234587536359)
        ·
          refine ⟨5421720635224851881304539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614480423483234587536359 5421720635224851881304539)
          ·
            refine ⟨8132580952837277821956809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421720635224851881304539 8132580952837277821956809)
            ·
              refine ⟨6099435714627958366467607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8132580952837277821956809 6099435714627958366467607)
              ·
                refine ⟨9149153571941937549701411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099435714627958366467607 9149153571941937549701411)
                ·
                  refine ⟨13723730357912906324552117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9149153571941937549701411 13723730357912906324552117)
                  ·
                    refine ⟨1286599721054334967926761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13723730357912906324552117 1286599721054334967926761)
                    ·
                      refine ⟨964949790790751225945071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286599721054334967926761 964949790790751225945071)
                      ·
                        rfl

theorem cell23_1879233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_1879233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879233 prefixEnd_1879233 := by exact prefixLift 1879233
  have htrace : WordTrace (prefixWord ++ tailWord_1879233) baseStart_1879233 baseEnd_1879233 := by
    simpa [prefixWord, tailWord_1879233, baseEnd_1879233] using wordTrace_append hprefix tailTrace_1879233
  have hstable : (prefixWord ++ tailWord_1879233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879233).length < 2 ^ (prefixWord ++ tailWord_1879233).sum := by decide
  have hdescent : baseEnd_1879233 < baseStart_1879233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879234 : List Nat := [3, 5, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_1879234 : Nat := 118140960795 + 1879234 * 2 ^ 59
def prefixEnd_1879234 : Nat := 4983230072969 + 3 ^ 40 * 1879234 * 2
def baseEnd_1879234 : Nat := 321650101423801907344189

theorem tailTrace_1879234 : CollatzResearch.WordTrace tailWord_1879234 prefixEnd_1879234 321650101423801907344189 := by
  unfold tailWord_1879234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17135323718465910115091189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45694196582575760306909837 17135323718465910115091189)
  ·
    refine ⟨1606436598606179073289799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17135323718465910115091189 1606436598606179073289799)
    ·
      refine ⟨2409654897909268609934699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606436598606179073289799 2409654897909268609934699)
      ·
        refine ⟨3614482346863902914902049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409654897909268609934699 3614482346863902914902049)
        ·
          refine ⟨2710861760147927186176537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3614482346863902914902049 2710861760147927186176537)
          ·
            refine ⟨2033146320110945389632403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710861760147927186176537 2033146320110945389632403)
            ·
              refine ⟨3049719480166418084448605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033146320110945389632403 3049719480166418084448605)
              ·
                refine ⟨1143644805062406781668227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049719480166418084448605 1143644805062406781668227)
                ·
                  refine ⟨1715467207593610172502341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143644805062406781668227 1715467207593610172502341)
                  ·
                    refine ⟨321650101423801907344189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1715467207593610172502341 321650101423801907344189)
                    ·
                      rfl

theorem cell23_1879234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_1879234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879234 prefixEnd_1879234 := by exact prefixLift 1879234
  have htrace : WordTrace (prefixWord ++ tailWord_1879234) baseStart_1879234 baseEnd_1879234 := by
    simpa [prefixWord, tailWord_1879234, baseEnd_1879234] using wordTrace_append hprefix tailTrace_1879234
  have hstable : (prefixWord ++ tailWord_1879234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879234).length < 2 ^ (prefixWord ++ tailWord_1879234).sum := by decide
  have hdescent : baseEnd_1879234 < baseStart_1879234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879249 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 3]
def baseStart_1879249 : Nat := 118140960795 + 1879249 * 2 ^ 59
def prefixEnd_1879249 : Nat := 4983230072969 + 3 ^ 40 * 1879249 * 2
def baseEnd_1879249 : Nat := 964958006481223163344997

theorem tailTrace_1879249 : CollatzResearch.WordTrace tailWord_1879249 prefixEnd_1879249 964958006481223163344997 := by
  unfold tailWord_1879249
  simp only [CollatzResearch.WordTrace]
  refine ⟨68541841968809298022160801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45694561312539532014773867 68541841968809298022160801)
  ·
    refine ⟨51406381476606973516620601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68541841968809298022160801 51406381476606973516620601)
    ·
      refine ⟨38554786107455230137465451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51406381476606973516620601 38554786107455230137465451)
      ·
        refine ⟨57832179161182845206198177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38554786107455230137465451 57832179161182845206198177)
        ·
          refine ⟨43374134370887133904648633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57832179161182845206198177 43374134370887133904648633)
          ·
            refine ⟨32530600778165350428486475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43374134370887133904648633 32530600778165350428486475)
            ·
              refine ⟨48795901167248025642729713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32530600778165350428486475 48795901167248025642729713)
              ·
                refine ⟨36596925875436019232047285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48795901167248025642729713 36596925875436019232047285)
                ·
                  refine ⟨3430961800822126803004433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36596925875436019232047285 3430961800822126803004433)
                  ·
                    refine ⟨2573221350616595102253325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3430961800822126803004433 2573221350616595102253325)
                    ·
                      refine ⟨964958006481223163344997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573221350616595102253325 964958006481223163344997)
                      ·
                        rfl

theorem cell23_1879249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_1879249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879249 prefixEnd_1879249 := by exact prefixLift 1879249
  have htrace : WordTrace (prefixWord ++ tailWord_1879249) baseStart_1879249 baseEnd_1879249 := by
    simpa [prefixWord, tailWord_1879249, baseEnd_1879249] using wordTrace_append hprefix tailTrace_1879249
  have hstable : (prefixWord ++ tailWord_1879249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879249).length < 2 ^ (prefixWord ++ tailWord_1879249).sum := by decide
  have hdescent : baseEnd_1879249 < baseStart_1879249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879263 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 3, 2, 2]
def baseStart_1879263 : Nat := 118140960795 + 1879263 * 2 ^ 59
def prefixEnd_1879263 : Nat := 4983230072969 + 3 ^ 40 * 1879263 * 2
def baseEnd_1879263 : Nat := 964965195210386108569933

theorem tailTrace_1879263 : CollatzResearch.WordTrace tailWord_1879263 prefixEnd_1879263 964965195210386108569933 := by
  unfold tailWord_1879263
  simp only [CollatzResearch.WordTrace]
  refine ⟨68542352590758578413170443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45694901727172385608780295 68542352590758578413170443)
  ·
    refine ⟨102813528886137867619755665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68542352590758578413170443 102813528886137867619755665)
    ·
      refine ⟨77110146664603400714816749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102813528886137867619755665 77110146664603400714816749)
      ·
        refine ⟨28916304999226275268056281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77110146664603400714816749 28916304999226275268056281)
        ·
          refine ⟨21687228749419706451042211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28916304999226275268056281 21687228749419706451042211)
          ·
            refine ⟨32530843124129559676563317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21687228749419706451042211 32530843124129559676563317)
            ·
              refine ⟨3049766542887146219677811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32530843124129559676563317 3049766542887146219677811)
              ·
                refine ⟨4574649814330719329516717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049766542887146219677811 4574649814330719329516717)
                ·
                  refine ⟨1715493680374019748568769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4574649814330719329516717 1715493680374019748568769)
                  ·
                    refine ⟨1286620260280514811426577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715493680374019748568769 1286620260280514811426577)
                    ·
                      refine ⟨964965195210386108569933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286620260280514811426577 964965195210386108569933)
                      ·
                        rfl

theorem cell23_1879263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_1879263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879263 prefixEnd_1879263 := by exact prefixLift 1879263
  have htrace : WordTrace (prefixWord ++ tailWord_1879263) baseStart_1879263 baseEnd_1879263 := by
    simpa [prefixWord, tailWord_1879263, baseEnd_1879263] using wordTrace_append hprefix tailTrace_1879263
  have hstable : (prefixWord ++ tailWord_1879263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879263).length < 2 ^ (prefixWord ++ tailWord_1879263).sum := by decide
  have hdescent : baseEnd_1879263 < baseStart_1879263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879283 : List Nat := [1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 3]
def baseStart_1879283 : Nat := 118140960795 + 1879283 * 2 ^ 59
def prefixEnd_1879283 : Nat := 4983230072969 + 3 ^ 40 * 1879283 * 2
def baseEnd_1879283 : Nat := 964975464823476030319841

theorem tailTrace_1879283 : CollatzResearch.WordTrace tailWord_1879283 prefixEnd_1879283 964975464823476030319841 := by
  unfold tailWord_1879283
  simp only [CollatzResearch.WordTrace]
  refine ⟨68543082050686121828898503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45695388033790747885932335 68543082050686121828898503)
  ·
    refine ⟨102814623076029182743347755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68543082050686121828898503 102814623076029182743347755)
    ·
      refine ⟨154221934614043774115021633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102814623076029182743347755 154221934614043774115021633)
      ·
        refine ⟨115666450960532830586266225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154221934614043774115021633 115666450960532830586266225)
        ·
          refine ⟨86749838220399622939699669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115666450960532830586266225 86749838220399622939699669)
          ·
            refine ⟨2033199333290616162649211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 86749838220399622939699669 2033199333290616162649211)
            ·
              refine ⟨3049798999935924243973817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033199333290616162649211 3049798999935924243973817)
              ·
                refine ⟨2287349249951943182980363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049798999935924243973817 2287349249951943182980363)
                ·
                  refine ⟨3431023874927914774470545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287349249951943182980363 3431023874927914774470545)
                  ·
                    refine ⟨2573267906195936080852909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431023874927914774470545 2573267906195936080852909)
                    ·
                      refine ⟨964975464823476030319841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573267906195936080852909 964975464823476030319841)
                      ·
                        rfl

theorem cell23_1879283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 1, 2, 3].length) (baseStart_1879283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879283 prefixEnd_1879283 := by exact prefixLift 1879283
  have htrace : WordTrace (prefixWord ++ tailWord_1879283) baseStart_1879283 baseEnd_1879283 := by
    simpa [prefixWord, tailWord_1879283, baseEnd_1879283] using wordTrace_append hprefix tailTrace_1879283
  have hstable : (prefixWord ++ tailWord_1879283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879283).length < 2 ^ (prefixWord ++ tailWord_1879283).sum := by decide
  have hdescent : baseEnd_1879283 < baseStart_1879283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879284 : List Nat := [2, 6, 1, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1879284 : Nat := 118140960795 + 1879284 * 2 ^ 59
def prefixEnd_1879284 : Nat := 4983230072969 + 3 ^ 40 * 1879284 * 2
def baseEnd_1879284 : Nat := 964975978304130526407337

theorem tailTrace_1879284 : CollatzResearch.WordTrace tailWord_1879284 prefixEnd_1879284 964975978304130526407337 := by
  unfold tailWord_1879284
  simp only [CollatzResearch.WordTrace]
  refine ⟨34271559261841249499842453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45695412349121665999789937 34271559261841249499842453)
  ·
    refine ⟨1606479340398808570305115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34271559261841249499842453 1606479340398808570305115)
    ·
      refine ⟨2409719010598212855457673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606479340398808570305115 2409719010598212855457673)
      ·
        refine ⟨1807289257948659641593255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409719010598212855457673 1807289257948659641593255)
        ·
          refine ⟨2710933886922989462389883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807289257948659641593255 2710933886922989462389883)
          ·
            refine ⟨4066400830384484193584825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710933886922989462389883 4066400830384484193584825)
            ·
              refine ⟨3049800622788363145188619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066400830384484193584825 3049800622788363145188619)
              ·
                refine ⟨4574700934182544717782929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3049800622788363145188619 4574700934182544717782929)
                ·
                  refine ⟨3431025700636908538337197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4574700934182544717782929 3431025700636908538337197)
                  ·
                    refine ⟨1286634637738840701876449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431025700636908538337197 1286634637738840701876449)
                    ·
                      refine ⟨964975978304130526407337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286634637738840701876449 964975978304130526407337)
                      ·
                        rfl

theorem cell23_1879284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1879284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879284 prefixEnd_1879284 := by exact prefixLift 1879284
  have htrace : WordTrace (prefixWord ++ tailWord_1879284) baseStart_1879284 baseEnd_1879284 := by
    simpa [prefixWord, tailWord_1879284, baseEnd_1879284] using wordTrace_append hprefix tailTrace_1879284
  have hstable : (prefixWord ++ tailWord_1879284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879284).length < 2 ^ (prefixWord ++ tailWord_1879284).sum := by decide
  have hdescent : baseEnd_1879284 < baseStart_1879284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879300 : List Nat := [2, 3, 2, 2, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1879300 : Nat := 118140960795 + 1879300 * 2 ^ 59
def prefixEnd_1879300 : Nat := 4983230072969 + 3 ^ 40 * 1879300 * 2
def baseEnd_1879300 : Nat := 964984193994602463807263

theorem tailTrace_1879300 : CollatzResearch.WordTrace tailWord_1879300 prefixEnd_1879300 964984193994602463807263 := by
  unfold tailWord_1879300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34271851045812266866133677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45695801394416355821511569 34271851045812266866133677)
  ·
    refine ⟨12851944142179600074800129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34271851045812266866133677 12851944142179600074800129)
    ·
      refine ⟨9638958106634700056100097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12851944142179600074800129 9638958106634700056100097)
      ·
        refine ⟨7229218579976025042075073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9638958106634700056100097 7229218579976025042075073)
        ·
          refine ⟨5421913934982018781556305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7229218579976025042075073 5421913934982018781556305)
          ·
            refine ⟨4066435451236514086167229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421913934982018781556305 4066435451236514086167229)
            ·
              refine ⟨1524913294213692782312711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066435451236514086167229 1524913294213692782312711)
              ·
                refine ⟨2287369941320539173469067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524913294213692782312711 2287369941320539173469067)
                ·
                  refine ⟨3431054911980808760203601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287369941320539173469067 3431054911980808760203601)
                  ·
                    refine ⟨2573291183985606570152701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431054911980808760203601 2573291183985606570152701)
                    ·
                      refine ⟨964984193994602463807263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573291183985606570152701 964984193994602463807263)
                      ·
                        rfl

theorem cell23_1879300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1879300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879300 prefixEnd_1879300 := by exact prefixLift 1879300
  have htrace : WordTrace (prefixWord ++ tailWord_1879300) baseStart_1879300 baseEnd_1879300 := by
    simpa [prefixWord, tailWord_1879300, baseEnd_1879300] using wordTrace_append hprefix tailTrace_1879300
  have hstable : (prefixWord ++ tailWord_1879300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879300).length < 2 ^ (prefixWord ++ tailWord_1879300).sum := by decide
  have hdescent : baseEnd_1879300 < baseStart_1879300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879313 : List Nat := [1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 3]
def baseStart_1879313 : Nat := 118140960795 + 1879313 * 2 ^ 59
def prefixEnd_1879313 : Nat := 4983230072969 + 3 ^ 40 * 1879313 * 2
def baseEnd_1879313 : Nat := 964990869243110912944703

theorem tailTrace_1879313 : CollatzResearch.WordTrace tailWord_1879313 prefixEnd_1879313 964990869243110912944703 := by
  unfold tailWord_1879313
  simp only [CollatzResearch.WordTrace]
  refine ⟨68544176240577436952490593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45696117493718291301660395 68544176240577436952490593)
  ·
    refine ⟨51408132180433077714367945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68544176240577436952490593 51408132180433077714367945)
    ·
      refine ⟨38556099135324808285775959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51408132180433077714367945 38556099135324808285775959)
      ·
        refine ⟨57834148702987212428663939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38556099135324808285775959 57834148702987212428663939)
        ·
          refine ⟨86751223054480818642995909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57834148702987212428663939 86751223054480818642995909)
          ·
            refine ⟨16265854322715153495561733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86751223054480818642995909 16265854322715153495561733)
            ·
              refine ⟨3049847685509091280417825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16265854322715153495561733 3049847685509091280417825)
              ·
                refine ⟨2287385764131818460313369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3049847685509091280417825 2287385764131818460313369)
                ·
                  refine ⟨1715539323098863845235027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287385764131818460313369 1715539323098863845235027)
                  ·
                    refine ⟨2573308984648295767852541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715539323098863845235027 2573308984648295767852541)
                    ·
                      refine ⟨964990869243110912944703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573308984648295767852541 964990869243110912944703)
                      ·
                        rfl

theorem cell23_1879313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_1879313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879313 prefixEnd_1879313 := by exact prefixLift 1879313
  have htrace : WordTrace (prefixWord ++ tailWord_1879313) baseStart_1879313 baseEnd_1879313 := by
    simpa [prefixWord, tailWord_1879313, baseEnd_1879313] using wordTrace_append hprefix tailTrace_1879313
  have hstable : (prefixWord ++ tailWord_1879313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879313).length < 2 ^ (prefixWord ++ tailWord_1879313).sum := by decide
  have hdescent : baseEnd_1879313 < baseStart_1879313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879319 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4]
def baseStart_1879319 : Nat := 118140960795 + 1879319 * 2 ^ 59
def prefixEnd_1879319 : Nat := 4983230072969 + 3 ^ 40 * 1879319 * 2
def baseEnd_1879319 : Nat := 964993950127037889469675

theorem tailTrace_1879319 : CollatzResearch.WordTrace tailWord_1879319 prefixEnd_1879319 964993950127037889469675 := by
  unfold tailWord_1879319
  simp only [CollatzResearch.WordTrace]
  refine ⟨68544395078555699977209011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45696263385703799984806007 68544395078555699977209011)
  ·
    refine ⟨102816592617833549965813517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68544395078555699977209011 102816592617833549965813517)
    ·
      refine ⟨38556222231687581237180069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102816592617833549965813517 38556222231687581237180069)
      ·
        refine ⟨7229291668441421481971263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38556222231687581237180069 7229291668441421481971263)
        ·
          refine ⟨10843937502662132222956895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7229291668441421481971263 10843937502662132222956895)
          ·
            refine ⟨16265906253993198334435343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843937502662132222956895 16265906253993198334435343)
            ·
              refine ⟨24398859380989797501653015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265906253993198334435343 24398859380989797501653015)
              ·
                refine ⟨36598289071484696252479523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24398859380989797501653015 36598289071484696252479523)
                ·
                  refine ⟨54897433607227044378719285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36598289071484696252479523 54897433607227044378719285)
                  ·
                    refine ⟨5146634400677535410504933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54897433607227044378719285 5146634400677535410504933)
                    ·
                      refine ⟨964993950127037889469675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5146634400677535410504933 964993950127037889469675)
                      ·
                        rfl

theorem cell23_1879319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_1879319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879319 prefixEnd_1879319 := by exact prefixLift 1879319
  have htrace : WordTrace (prefixWord ++ tailWord_1879319) baseStart_1879319 baseEnd_1879319 := by
    simpa [prefixWord, tailWord_1879319, baseEnd_1879319] using wordTrace_append hprefix tailTrace_1879319
  have hstable : (prefixWord ++ tailWord_1879319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879319).length < 2 ^ (prefixWord ++ tailWord_1879319).sum := by decide
  have hdescent : baseEnd_1879319 < baseStart_1879319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879357 : List Nat := [1, 4, 1, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_1879357 : Nat := 118140960795 + 1879357 * 2 ^ 59
def prefixEnd_1879357 : Nat := 4983230072969 + 3 ^ 40 * 1879357 * 2
def baseEnd_1879357 : Nat := 965013462391908740794501

theorem tailTrace_1879357 : CollatzResearch.WordTrace tailWord_1879357 prefixEnd_1879357 965013462391908740794501 := by
  unfold tailWord_1879357
  simp only [CollatzResearch.WordTrace]
  refine ⟨68545781052418032467092325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45697187368278688311394883 68545781052418032467092325)
  ·
    refine ⟨12852333947328381087579811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68545781052418032467092325 12852333947328381087579811)
    ·
      refine ⟨19278500920992571631369717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12852333947328381087579811 19278500920992571631369717)
      ·
        refine ⟨1807359461343053590440911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19278500920992571631369717 1807359461343053590440911)
        ·
          refine ⟨2711039192014580385661367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807359461343053590440911 2711039192014580385661367)
          ·
            refine ⟨4066558788021870578492051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711039192014580385661367 4066558788021870578492051)
            ·
              refine ⟨6099838182032805867738077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066558788021870578492051 6099838182032805867738077)
              ·
                refine ⟨2287439318262302200401779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6099838182032805867738077 2287439318262302200401779)
                ·
                  refine ⟨3431158977393453300602669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287439318262302200401779 3431158977393453300602669)
                  ·
                    refine ⟨1286684616522544987726001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431158977393453300602669 1286684616522544987726001)
                    ·
                      refine ⟨965013462391908740794501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286684616522544987726001 965013462391908740794501)
                      ·
                        rfl

theorem cell23_1879357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_1879357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879357 prefixEnd_1879357 := by exact prefixLift 1879357
  have htrace : WordTrace (prefixWord ++ tailWord_1879357) baseStart_1879357 baseEnd_1879357 := by
    simpa [prefixWord, tailWord_1879357, baseEnd_1879357] using wordTrace_append hprefix tailTrace_1879357
  have hstable : (prefixWord ++ tailWord_1879357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879357).length < 2 ^ (prefixWord ++ tailWord_1879357).sum := by decide
  have hdescent : baseEnd_1879357 < baseStart_1879357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879376 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 5]
def baseStart_1879376 : Nat := 118140960795 + 1879376 * 2 ^ 59
def prefixEnd_1879376 : Nat := 4983230072969 + 3 ^ 40 * 1879376 * 2
def baseEnd_1879376 : Nat := 107224802058260462939657

theorem tailTrace_1879376 : CollatzResearch.WordTrace tailWord_1879376 prefixEnd_1879376 107224802058260462939657 := by
  unfold tailWord_1879376
  simp only [CollatzResearch.WordTrace]
  refine ⟨34273237019674599356016991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45697649359566132474689321 34273237019674599356016991)
  ·
    refine ⟨51409855529511899034025487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34273237019674599356016991 51409855529511899034025487)
    ·
      refine ⟨77114783294267848551038231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51409855529511899034025487 77114783294267848551038231)
      ·
        refine ⟨115672174941401772826557347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77114783294267848551038231 115672174941401772826557347)
        ·
          refine ⟨173508262412102659239836021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115672174941401772826557347 173508262412102659239836021)
          ·
            refine ⟨16266399601134624303734627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173508262412102659239836021 16266399601134624303734627)
            ·
              refine ⟨24399599401701936455601941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16266399601134624303734627 24399599401701936455601941)
              ·
                refine ⟨1143731221954778271356341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24399599401701936455601941 1143731221954778271356341)
                ·
                  refine ⟨107224802058260462939657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1143731221954778271356341 107224802058260462939657)
                  ·
                    rfl

theorem cell23_1879376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 5].length) (baseStart_1879376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879376 prefixEnd_1879376 := by exact prefixLift 1879376
  have htrace : WordTrace (prefixWord ++ tailWord_1879376) baseStart_1879376 baseEnd_1879376 := by
    simpa [prefixWord, tailWord_1879376, baseEnd_1879376] using wordTrace_append hprefix tailTrace_1879376
  have hstable : (prefixWord ++ tailWord_1879376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879376).length < 2 ^ (prefixWord ++ tailWord_1879376).sum := by decide
  have hdescent : baseEnd_1879376 < baseStart_1879376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879386 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3]
def baseStart_1879386 : Nat := 118140960795 + 1879386 * 2 ^ 59
def prefixEnd_1879386 : Nat := 4983230072969 + 3 ^ 40 * 1879386 * 2
def baseEnd_1879386 : Nat := 965028353330889127331867

theorem tailTrace_1879386 : CollatzResearch.WordTrace tailWord_1879386 prefixEnd_1879386 965028353330889127331867 := by
  unfold tailWord_1879386
  simp only [CollatzResearch.WordTrace]
  refine ⟨17136709692328242604974503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45697892512875313613265341 17136709692328242604974503)
  ·
    refine ⟨25705064538492363907461755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17136709692328242604974503 25705064538492363907461755)
    ·
      refine ⟨38557596807738545861192633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25705064538492363907461755 38557596807738545861192633)
      ·
        refine ⟨28918197605803909395894475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38557596807738545861192633 28918197605803909395894475)
        ·
          refine ⟨43377296408705864093841713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28918197605803909395894475 43377296408705864093841713)
          ·
            refine ⟨32532972306529398070381285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43377296408705864093841713 32532972306529398070381285)
            ·
              refine ⟨6099932307474262138196491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32532972306529398070381285 6099932307474262138196491)
              ·
                refine ⟨9149898461211393207294737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6099932307474262138196491 9149898461211393207294737)
                ·
                  refine ⟨6862423845908544905471053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9149898461211393207294737 6862423845908544905471053)
                  ·
                    refine ⟨2573408942215704339551645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6862423845908544905471053 2573408942215704339551645)
                    ·
                      refine ⟨965028353330889127331867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573408942215704339551645 965028353330889127331867)
                      ·
                        rfl

theorem cell23_1879386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_1879386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879386 prefixEnd_1879386 := by exact prefixLift 1879386
  have htrace : WordTrace (prefixWord ++ tailWord_1879386) baseStart_1879386 baseEnd_1879386 := by
    simpa [prefixWord, tailWord_1879386, baseEnd_1879386] using wordTrace_append hprefix tailTrace_1879386
  have hstable : (prefixWord ++ tailWord_1879386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879386).length < 2 ^ (prefixWord ++ tailWord_1879386).sum := by decide
  have hdescent : baseEnd_1879386 < baseStart_1879386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879486 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1879486 : Nat := 118140960795 + 1879486 * 2 ^ 59
def prefixEnd_1879486 : Nat := 4983230072969 + 3 ^ 40 * 1879486 * 2
def baseEnd_1879486 : Nat := 965079701396338736081407

theorem tailTrace_1879486 : CollatzResearch.WordTrace tailWord_1879486 prefixEnd_1879486 965079701396338736081407 := by
  unfold tailWord_1879486
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568810758618835937317289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45700324045967124999025541 8568810758618835937317289)
  ·
    refine ⟨6426608068964126952987967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8568810758618835937317289 6426608068964126952987967)
    ·
      refine ⟨9639912103446190429481951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426608068964126952987967 9639912103446190429481951)
      ·
        refine ⟨14459868155169285644222927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9639912103446190429481951 14459868155169285644222927)
        ·
          refine ⟨21689802232753928466334391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459868155169285644222927 21689802232753928466334391)
          ·
            refine ⟨32534703349130892699501587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21689802232753928466334391 32534703349130892699501587)
            ·
              refine ⟨48802055023696339049252381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32534703349130892699501587 48802055023696339049252381)
              ·
                refine ⟨18300770633886127143469643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48802055023696339049252381 18300770633886127143469643)
                ·
                  refine ⟨27451155950829190715204465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18300770633886127143469643 27451155950829190715204465)
                  ·
                    refine ⟨20588366963121893036403349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27451155950829190715204465 20588366963121893036403349)
                    ·
                      refine ⟨965079701396338736081407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20588366963121893036403349 965079701396338736081407)
                      ·
                        rfl

theorem cell23_1879486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1879486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879486 prefixEnd_1879486 := by exact prefixLift 1879486
  have htrace : WordTrace (prefixWord ++ tailWord_1879486) baseStart_1879486 baseEnd_1879486 := by
    simpa [prefixWord, tailWord_1879486, baseEnd_1879486] using wordTrace_append hprefix tailTrace_1879486
  have hstable : (prefixWord ++ tailWord_1879486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879486).length < 2 ^ (prefixWord ++ tailWord_1879486).sum := by decide
  have hdescent : baseEnd_1879486 < baseStart_1879486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879496 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 5, 5]
def baseStart_1879496 : Nat := 118140960795 + 1879496 * 2 ^ 59
def prefixEnd_1879496 : Nat := 4983230072969 + 3 ^ 40 * 1879496 * 2
def baseEnd_1879496 : Nat := 321694945400961232318787

theorem tailTrace_1879496 : CollatzResearch.WordTrace tailWord_1879496 prefixEnd_1879496 321694945400961232318787 := by
  unfold tailWord_1879496
  simp only [CollatzResearch.WordTrace]
  refine ⟨34275425399457229603201171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45700567199276306137601561 34275425399457229603201171)
  ·
    refine ⟨51413138099185844404801757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34275425399457229603201171 51413138099185844404801757)
    ·
      refine ⟨19279926787194691651800659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51413138099185844404801757 19279926787194691651800659)
      ·
        refine ⟨28919890180792037477700989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19279926787194691651800659 28919890180792037477700989)
        ·
          refine ⟨10844958817797014054137871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28919890180792037477700989 10844958817797014054137871)
          ·
            refine ⟨16267438226695521081206807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10844958817797014054137871 16267438226695521081206807)
            ·
              refine ⟨24401157340043281621810211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16267438226695521081206807 24401157340043281621810211)
              ·
                refine ⟨36601736010064922432715317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24401157340043281621810211 36601736010064922432715317)
                ·
                  refine ⟨3431412750943586478067061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36601736010064922432715317 3431412750943586478067061)
                  ·
                    refine ⟨321694945400961232318787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3431412750943586478067061 321694945400961232318787)
                    ·
                      rfl

theorem cell23_1879496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 5, 5].length) (baseStart_1879496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879496 prefixEnd_1879496 := by exact prefixLift 1879496
  have htrace : WordTrace (prefixWord ++ tailWord_1879496) baseStart_1879496 baseEnd_1879496 := by
    simpa [prefixWord, tailWord_1879496, baseEnd_1879496] using wordTrace_append hprefix tailTrace_1879496
  have hstable : (prefixWord ++ tailWord_1879496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879496).length < 2 ^ (prefixWord ++ tailWord_1879496).sum := by decide
  have hdescent : baseEnd_1879496 < baseStart_1879496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879503 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 4, 3, 2]
def baseStart_1879503 : Nat := 118140960795 + 1879503 * 2 ^ 59
def prefixEnd_1879503 : Nat := 4983230072969 + 3 ^ 40 * 1879503 * 2
def baseEnd_1879503 : Nat := 965088430567465169568829

theorem tailTrace_1879503 : CollatzResearch.WordTrace tailWord_1879503 prefixEnd_1879503 965088430567465169568829 := by
  unfold tailWord_1879503
  simp only [CollatzResearch.WordTrace]
  refine ⟨68551106109889099401907163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45700737406592732934604775 68551106109889099401907163)
  ·
    refine ⟨102826659164833649102860745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68551106109889099401907163 102826659164833649102860745)
    ·
      refine ⟨77119994373625236827145559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102826659164833649102860745 77119994373625236827145559)
      ·
        refine ⟨115679991560437855240718339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77119994373625236827145559 115679991560437855240718339)
        ·
          refine ⟨173519987340656782861077509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115679991560437855240718339 173519987340656782861077509)
          ·
            refine ⟨32534997626373146786452033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173519987340656782861077509 32534997626373146786452033)
            ·
              refine ⟨24401248219779860089839025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32534997626373146786452033 24401248219779860089839025)
              ·
                refine ⟨18300936164834895067379269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24401248219779860089839025 18300936164834895067379269)
                ·
                  refine ⟨3431425530906542825133613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18300936164834895067379269 3431425530906542825133613)
                  ·
                    refine ⟨1286784574089953559425105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431425530906542825133613 1286784574089953559425105)
                    ·
                      refine ⟨965088430567465169568829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286784574089953559425105 965088430567465169568829)
                      ·
                        rfl

theorem cell23_1879503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 4, 3, 2].length) (baseStart_1879503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879503 prefixEnd_1879503 := by exact prefixLift 1879503
  have htrace : WordTrace (prefixWord ++ tailWord_1879503) baseStart_1879503 baseEnd_1879503 := by
    simpa [prefixWord, tailWord_1879503, baseEnd_1879503] using wordTrace_append hprefix tailTrace_1879503
  have hstable : (prefixWord ++ tailWord_1879503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879503).length < 2 ^ (prefixWord ++ tailWord_1879503).sum := by decide
  have hdescent : baseEnd_1879503 < baseStart_1879503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879527 : List Nat := [1, 1, 5, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1879527 : Nat := 118140960795 + 1879527 * 2 ^ 59
def prefixEnd_1879527 : Nat := 4983230072969 + 3 ^ 40 * 1879527 * 2
def baseEnd_1879527 : Nat := 965100754103173075668719

theorem tailTrace_1879527 : CollatzResearch.WordTrace tailWord_1879527 prefixEnd_1879527 965100754103173075668719 := by
  unfold tailWord_1879527
  simp only [CollatzResearch.WordTrace]
  refine ⟨68551981461802151500780835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45701320974534767667187223 68551981461802151500780835)
  ·
    refine ⟨102827972192703227251171253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68551981461802151500780835 102827972192703227251171253)
    ·
      refine ⟨9640122393065927554797305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102827972192703227251171253 9640122393065927554797305)
      ·
        refine ⟨7230091794799445666097979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9640122393065927554797305 7230091794799445666097979)
        ·
          refine ⟨10845137692199168499146969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230091794799445666097979 10845137692199168499146969)
          ·
            refine ⟨8133853269149376374360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845137692199168499146969 8133853269149376374360227)
            ·
              refine ⟨12200779903724064561540341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8133853269149376374360227 12200779903724064561540341)
              ·
                refine ⟨1143823115974131052644407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12200779903724064561540341 1143823115974131052644407)
                ·
                  refine ⟨1715734673961196578966611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1143823115974131052644407 1715734673961196578966611)
                  ·
                    refine ⟨2573602010941794868449917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715734673961196578966611 2573602010941794868449917)
                    ·
                      refine ⟨965100754103173075668719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573602010941794868449917 965100754103173075668719)
                      ·
                        rfl

theorem cell23_1879527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1879527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879527 prefixEnd_1879527 := by exact prefixLift 1879527
  have htrace : WordTrace (prefixWord ++ tailWord_1879527) baseStart_1879527 baseEnd_1879527 := by
    simpa [prefixWord, tailWord_1879527, baseEnd_1879527] using wordTrace_append hprefix tailTrace_1879527
  have hstable : (prefixWord ++ tailWord_1879527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879527).length < 2 ^ (prefixWord ++ tailWord_1879527).sum := by decide
  have hdescent : baseEnd_1879527 < baseStart_1879527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879530 : List Nat := [3, 1, 3, 1, 4, 1, 1, 3, 1, 5]
def baseStart_1879530 : Nat := 118140960795 + 1879530 * 2 ^ 59
def prefixEnd_1879530 : Nat := 4983230072969 + 3 ^ 40 * 1879530 * 2
def baseEnd_1879530 : Nat := 321700764848378854643735

theorem tailTrace_1879530 : CollatzResearch.WordTrace tailWord_1879530 prefixEnd_1879530 321700764848378854643735 := by
  unfold tailWord_1879530
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138022720197820753285011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45701393920527522008760029 17138022720197820753285011)
  ·
    refine ⟨25707034080296731129927517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138022720197820753285011 25707034080296731129927517)
    ·
      refine ⟨9640137780111274173722819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25707034080296731129927517 9640137780111274173722819)
      ·
        refine ⟨14460206670166911260584229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640137780111274173722819 14460206670166911260584229)
        ·
          refine ⟨2711288750656295861359543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14460206670166911260584229 2711288750656295861359543)
          ·
            refine ⟨4066933125984443792039315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711288750656295861359543 4066933125984443792039315)
            ·
              refine ⟨6100399688976665688058973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066933125984443792039315 6100399688976665688058973)
              ·
                refine ⟨2287649883366249633022115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100399688976665688058973 2287649883366249633022115)
                ·
                  refine ⟨3431474825049374449533173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287649883366249633022115 3431474825049374449533173)
                  ·
                    refine ⟨321700764848378854643735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3431474825049374449533173 321700764848378854643735)
                    ·
                      rfl

theorem cell23_1879530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 1, 5].length) (baseStart_1879530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879530 prefixEnd_1879530 := by exact prefixLift 1879530
  have htrace : WordTrace (prefixWord ++ tailWord_1879530) baseStart_1879530 baseEnd_1879530 := by
    simpa [prefixWord, tailWord_1879530, baseEnd_1879530] using wordTrace_append hprefix tailTrace_1879530
  have hstable : (prefixWord ++ tailWord_1879530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879530).length < 2 ^ (prefixWord ++ tailWord_1879530).sum := by decide
  have hdescent : baseEnd_1879530 < baseStart_1879530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879543 : List Nat := [1, 1, 3, 1, 1, 1, 1, 8, 2, 4]
def baseStart_1879543 : Nat := 118140960795 + 1879543 * 2 ^ 59
def prefixEnd_1879543 : Nat := 4983230072969 + 3 ^ 40 * 1879543 * 2
def baseEnd_1879543 : Nat := 321702989931215004356215

theorem tailTrace_1879543 : CollatzResearch.WordTrace tailWord_1879543 prefixEnd_1879543 321702989931215004356215 := by
  unfold tailWord_1879543
  simp only [CollatzResearch.WordTrace]
  refine ⟨68552565029744186233363283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45701710019829457488908855 68552565029744186233363283)
  ·
    refine ⟨102828847544616279350044925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68552565029744186233363283 102828847544616279350044925)
    ·
      refine ⟨38560817829231104756266847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102828847544616279350044925 38560817829231104756266847)
      ·
        refine ⟨57841226743846657134400271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38560817829231104756266847 57841226743846657134400271)
        ·
          refine ⟨86761840115769985701600407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57841226743846657134400271 86761840115769985701600407)
          ·
            refine ⟨130142760173654978552400611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86761840115769985701600407 130142760173654978552400611)
            ·
              refine ⟨195214140260482467828600917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130142760173654978552400611 195214140260482467828600917)
              ·
                refine ⟨2287665706177528919866417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 195214140260482467828600917 2287665706177528919866417)
                ·
                  refine ⟨1715749279633146689899813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287665706177528919866417 1715749279633146689899813)
                  ·
                    refine ⟨321702989931215004356215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1715749279633146689899813 321702989931215004356215)
                    ·
                      rfl

theorem cell23_1879543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 8, 2, 4].length) (baseStart_1879543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879543 prefixEnd_1879543 := by exact prefixLift 1879543
  have htrace : WordTrace (prefixWord ++ tailWord_1879543) baseStart_1879543 baseEnd_1879543 := by
    simpa [prefixWord, tailWord_1879543, baseEnd_1879543] using wordTrace_append hprefix tailTrace_1879543
  have hstable : (prefixWord ++ tailWord_1879543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879543).length < 2 ^ (prefixWord ++ tailWord_1879543).sum := by decide
  have hdescent : baseEnd_1879543 < baseStart_1879543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879546 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_1879546 : Nat := 118140960795 + 1879546 * 2 ^ 59
def prefixEnd_1879546 : Nat := 4983230072969 + 3 ^ 40 * 1879546 * 2
def baseEnd_1879546 : Nat := 965110510235608501331131

theorem tailTrace_1879546 : CollatzResearch.WordTrace tailWord_1879546 prefixEnd_1879546 965110510235608501331131 := by
  unfold tailWord_1879546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138168612183329436430623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45701782965822211830481661 17138168612183329436430623)
  ·
    refine ⟨25707252918274994154645935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138168612183329436430623 25707252918274994154645935)
    ·
      refine ⟨38560879377412491231968903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25707252918274994154645935 38560879377412491231968903)
      ·
        refine ⟨57841319066118736847953355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38560879377412491231968903 57841319066118736847953355)
        ·
          refine ⟨86761978599178105271930033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57841319066118736847953355 86761978599178105271930033)
          ·
            refine ⟨65071483949383578953947525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86761978599178105271930033 65071483949383578953947525)
            ·
              refine ⟨12200903240509421053865161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65071483949383578953947525 12200903240509421053865161)
              ·
                refine ⟨9150677430382065790398871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12200903240509421053865161 9150677430382065790398871)
                ·
                  refine ⟨13726016145573098685598307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9150677430382065790398871 13726016145573098685598307)
                  ·
                    refine ⟨20589024218359648028397461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13726016145573098685598307 20589024218359648028397461)
                    ·
                      refine ⟨965110510235608501331131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20589024218359648028397461 965110510235608501331131)
                      ·
                        rfl

theorem cell23_1879546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_1879546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879546 prefixEnd_1879546 := by exact prefixLift 1879546
  have htrace : WordTrace (prefixWord ++ tailWord_1879546) baseStart_1879546 baseEnd_1879546 := by
    simpa [prefixWord, tailWord_1879546, baseEnd_1879546] using wordTrace_append hprefix tailTrace_1879546
  have hstable : (prefixWord ++ tailWord_1879546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879546).length < 2 ^ (prefixWord ++ tailWord_1879546).sum := by decide
  have hdescent : baseEnd_1879546 < baseStart_1879546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879563 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6]
def baseStart_1879563 : Nat := 118140960795 + 1879563 * 2 ^ 59
def prefixEnd_1879563 : Nat := 4983230072969 + 3 ^ 40 * 1879563 * 2
def baseEnd_1879563 : Nat := 965119239406734934818553

theorem tailTrace_1879563 : CollatzResearch.WordTrace tailWord_1879563 prefixEnd_1879563 965119239406734934818553 := by
  unfold tailWord_1879563
  simp only [CollatzResearch.WordTrace]
  refine ⟨68553294489671729649091343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45702196326447819766060895 68553294489671729649091343)
  ·
    refine ⟨102829941734507594473637015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68553294489671729649091343 102829941734507594473637015)
    ·
      refine ⟨154244912601761391710455523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102829941734507594473637015 154244912601761391710455523)
      ·
        refine ⟨231367368902642087565683285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154244912601761391710455523 231367368902642087565683285)
        ·
          refine ⟨2711336354327836963660351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 231367368902642087565683285 2711336354327836963660351)
          ·
            refine ⟨4067004531491755445490527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711336354327836963660351 4067004531491755445490527)
            ·
              refine ⟨6100506797237633168235791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067004531491755445490527 6100506797237633168235791)
              ·
                refine ⟨9150760195856449752353687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6100506797237633168235791 9150760195856449752353687)
                ·
                  refine ⟨13726140293784674628530531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9150760195856449752353687 13726140293784674628530531)
                  ·
                    refine ⟨20589210440677011942795797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13726140293784674628530531 20589210440677011942795797)
                    ·
                      refine ⟨965119239406734934818553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20589210440677011942795797 965119239406734934818553)
                      ·
                        rfl

theorem cell23_1879563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 1, 1, 6].length) (baseStart_1879563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879563 prefixEnd_1879563 := by exact prefixLift 1879563
  have htrace : WordTrace (prefixWord ++ tailWord_1879563) baseStart_1879563 baseEnd_1879563 := by
    simpa [prefixWord, tailWord_1879563, baseEnd_1879563] using wordTrace_append hprefix tailTrace_1879563
  have hstable : (prefixWord ++ tailWord_1879563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879563).length < 2 ^ (prefixWord ++ tailWord_1879563).sum := by decide
  have hdescent : baseEnd_1879563 < baseStart_1879563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879573 : List Nat := [1, 3, 2, 1, 3, 2, 4, 7]
def baseStart_1879573 : Nat := 118140960795 + 1879573 * 2 ^ 59
def prefixEnd_1879573 : Nat := 4983230072969 + 3 ^ 40 * 1879573 * 2
def baseEnd_1879573 : Nat := 35745347193084440581241

theorem tailTrace_1879573 : CollatzResearch.WordTrace tailWord_1879573 prefixEnd_1879573 35745347193084440581241 := by
  unfold tailWord_1879573
  simp only [CollatzResearch.WordTrace]
  refine ⟨68553659219635501356955373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45702439479757000904636915 68553659219635501356955373)
  ·
    refine ⟨25707622207363313008858265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68553659219635501356955373 25707622207363313008858265)
    ·
      refine ⟨19280716655522484756643699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25707622207363313008858265 19280716655522484756643699)
      ·
        refine ⟨28921074983283727134965549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19280716655522484756643699 28921074983283727134965549)
        ·
          refine ⟨10845403118731397675612081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28921074983283727134965549 10845403118731397675612081)
          ·
            refine ⟨8134052339048548256709061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845403118731397675612081 8134052339048548256709061)
            ·
              refine ⟨1525134813571602798132949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8134052339048548256709061 1525134813571602798132949)
              ·
                refine ⟨35745347193084440581241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1525134813571602798132949 35745347193084440581241)
                ·
                  rfl

theorem cell23_1879573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 7].length) (baseStart_1879573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879573 prefixEnd_1879573 := by exact prefixLift 1879573
  have htrace : WordTrace (prefixWord ++ tailWord_1879573) baseStart_1879573 baseEnd_1879573 := by
    simpa [prefixWord, tailWord_1879573, baseEnd_1879573] using wordTrace_append hprefix tailTrace_1879573
  have hstable : (prefixWord ++ tailWord_1879573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879573).length < 2 ^ (prefixWord ++ tailWord_1879573).sum := by decide
  have hdescent : baseEnd_1879573 < baseStart_1879573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879583 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1879583 : Nat := 118140960795 + 1879583 * 2 ^ 59
def prefixEnd_1879583 : Nat := 4983230072969 + 3 ^ 40 * 1879583 * 2
def baseEnd_1879583 : Nat := 965129509019824856568461

theorem tailTrace_1879583 : CollatzResearch.WordTrace tailWord_1879583 prefixEnd_1879583 965129509019824856568461 := by
  unfold tailWord_1879583
  simp only [CollatzResearch.WordTrace]
  refine ⟨68554023949599273064819403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45702682633066182043212935 68554023949599273064819403)
  ·
    refine ⟨102831035924398909597229105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68554023949599273064819403 102831035924398909597229105)
    ·
      refine ⟨77123276943299182197921829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102831035924398909597229105 77123276943299182197921829)
      ·
        refine ⟨14460614426868596662110343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77123276943299182197921829 14460614426868596662110343)
        ·
          refine ⟨21690921640302894993165515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14460614426868596662110343 21690921640302894993165515)
          ·
            refine ⟨32536382460454342489748273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21690921640302894993165515 32536382460454342489748273)
            ·
              refine ⟨24402286845340756867311205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32536382460454342489748273 24402286845340756867311205)
              ·
                refine ⟨4575428783501391912620851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24402286845340756867311205 4575428783501391912620851)
                ·
                  refine ⟨6863143175252087868931277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4575428783501391912620851 6863143175252087868931277)
                  ·
                    refine ⟨2573678690719532950849229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6863143175252087868931277 2573678690719532950849229)
                    ·
                      refine ⟨965129509019824856568461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573678690719532950849229 965129509019824856568461)
                      ·
                        rfl

theorem cell23_1879583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1879583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879583 prefixEnd_1879583 := by exact prefixLift 1879583
  have htrace : WordTrace (prefixWord ++ tailWord_1879583) baseStart_1879583 baseEnd_1879583 := by
    simpa [prefixWord, tailWord_1879583, baseEnd_1879583] using wordTrace_append hprefix tailTrace_1879583
  have hstable : (prefixWord ++ tailWord_1879583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879583).length < 2 ^ (prefixWord ++ tailWord_1879583).sum := by decide
  have hdescent : baseEnd_1879583 < baseStart_1879583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879600 : List Nat := [2, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3]
def baseStart_1879600 : Nat := 118140960795 + 1879600 * 2 ^ 59
def prefixEnd_1879600 : Nat := 4983230072969 + 3 ^ 40 * 1879600 * 2
def baseEnd_1879600 : Nat := 965138238190951290055883

theorem tailTrace_1879600 : CollatzResearch.WordTrace tailWord_1879600 prefixEnd_1879600 965138238190951290055883 := by
  unfold tailWord_1879600
  simp only [CollatzResearch.WordTrace]
  refine ⟨34277321995268842484094127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45703095993691789978792169 34277321995268842484094127)
  ·
    refine ⟨51415982992903263726141191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34277321995268842484094127 51415982992903263726141191)
    ·
      refine ⟨77123974489354895589211787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51415982992903263726141191 77123974489354895589211787)
      ·
        refine ⟨115685961734032343383817681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77123974489354895589211787 115685961734032343383817681)
        ·
          refine ⟨86764471300524257537863261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115685961734032343383817681 86764471300524257537863261)
          ·
            refine ⟨32536676737696596576698723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86764471300524257537863261 32536676737696596576698723)
            ·
              refine ⟨48805015106544894865048085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32536676737696596576698723 48805015106544894865048085)
              ·
                refine ⟨2287735083119291946799129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48805015106544894865048085 2287735083119291946799129)
                ·
                  refine ⟨1715801312339468960099347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287735083119291946799129 1715801312339468960099347)
                  ·
                    refine ⟨2573701968509203440149021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715801312339468960099347 2573701968509203440149021)
                    ·
                      refine ⟨965138238190951290055883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573701968509203440149021 965138238190951290055883)
                      ·
                        rfl

theorem cell23_1879600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 6, 2, 1, 3].length) (baseStart_1879600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879600 prefixEnd_1879600 := by exact prefixLift 1879600
  have htrace : WordTrace (prefixWord ++ tailWord_1879600) baseStart_1879600 baseEnd_1879600 := by
    simpa [prefixWord, tailWord_1879600, baseEnd_1879600] using wordTrace_append hprefix tailTrace_1879600
  have hstable : (prefixWord ++ tailWord_1879600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879600).length < 2 ^ (prefixWord ++ tailWord_1879600).sum := by decide
  have hdescent : baseEnd_1879600 < baseStart_1879600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879610 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2]
def baseStart_1879610 : Nat := 118140960795 + 1879610 * 2 ^ 59
def prefixEnd_1879610 : Nat := 4983230072969 + 3 ^ 40 * 1879610 * 2
def baseEnd_1879610 : Nat := 965143372997496250930837

theorem tailTrace_1879610 : CollatzResearch.WordTrace tailWord_1879610 prefixEnd_1879610 965143372997496250930837 := by
  unfold tailWord_1879610
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138752180125364169013071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45703339147000971117368189 17138752180125364169013071)
  ·
    refine ⟨25708128270188046253519607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17138752180125364169013071 25708128270188046253519607)
    ·
      refine ⟨38562192405282069380279411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25708128270188046253519607 38562192405282069380279411)
      ·
        refine ⟨57843288607923104070419117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38562192405282069380279411 57843288607923104070419117)
        ·
          refine ⟨21691233227971164026407169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57843288607923104070419117 21691233227971164026407169)
          ·
            refine ⟨16268424920978373019805377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21691233227971164026407169 16268424920978373019805377)
            ·
              refine ⟨12201318690733779764854033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16268424920978373019805377 12201318690733779764854033)
              ·
                refine ⟨9150989018050334823640525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12201318690733779764854033 9150989018050334823640525)
                ·
                  refine ⟨3431620881768875558865197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9150989018050334823640525 3431620881768875558865197)
                  ·
                    refine ⟨1286857830663328334574449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431620881768875558865197 1286857830663328334574449)
                    ·
                      refine ⟨965143372997496250930837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286857830663328334574449 965143372997496250930837)
                      ·
                        rfl

theorem cell23_1879610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 3, 3, 2].length) (baseStart_1879610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879610 prefixEnd_1879610 := by exact prefixLift 1879610
  have htrace : WordTrace (prefixWord ++ tailWord_1879610) baseStart_1879610 baseEnd_1879610 := by
    simpa [prefixWord, tailWord_1879610, baseEnd_1879610] using wordTrace_append hprefix tailTrace_1879610
  have hstable : (prefixWord ++ tailWord_1879610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879610).length < 2 ^ (prefixWord ++ tailWord_1879610).sum := by decide
  have hdescent : baseEnd_1879610 < baseStart_1879610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879616 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 1, 8]
def baseStart_1879616 : Nat := 118140960795 + 1879616 * 2 ^ 59
def prefixEnd_1879616 : Nat := 4983230072969 + 3 ^ 40 * 1879616 * 2
def baseEnd_1879616 : Nat := 321715484627141075818603

theorem tailTrace_1879616 : CollatzResearch.WordTrace tailWord_1879616 prefixEnd_1879616 321715484627141075818603 := by
  unfold tailWord_1879616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34277613779239859850385351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45703485038986479800513801 34277613779239859850385351)
  ·
    refine ⟨51416420668859789775578027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34277613779239859850385351 51416420668859789775578027)
    ·
      refine ⟨77124631003289684663367041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51416420668859789775578027 77124631003289684663367041)
      ·
        refine ⟨57843473252467263497525281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77124631003289684663367041 57843473252467263497525281)
        ·
          refine ⟨43382604939350447623143961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57843473252467263497525281 43382604939350447623143961)
          ·
            refine ⟨32536953704512835717357971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43382604939350447623143961 32536953704512835717357971)
            ·
              refine ⟨48805430556769253576036957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32536953704512835717357971 48805430556769253576036957)
              ·
                refine ⟨18302036458788470091013859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48805430556769253576036957 18302036458788470091013859)
                ·
                  refine ⟨27453054688182705136520789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18302036458788470091013859 27453054688182705136520789)
                  ·
                    refine ⟨321715484627141075818603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 27453054688182705136520789 321715484627141075818603)
                    ·
                      rfl

theorem cell23_1879616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 1, 8].length) (baseStart_1879616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879616 prefixEnd_1879616 := by exact prefixLift 1879616
  have htrace : WordTrace (prefixWord ++ tailWord_1879616) baseStart_1879616 baseEnd_1879616 := by
    simpa [prefixWord, tailWord_1879616, baseEnd_1879616] using wordTrace_append hprefix tailTrace_1879616
  have hstable : (prefixWord ++ tailWord_1879616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879616).length < 2 ^ (prefixWord ++ tailWord_1879616).sum := by decide
  have hdescent : baseEnd_1879616 < baseStart_1879616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879617 : List Nat := [1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 3]
def baseStart_1879617 : Nat := 118140960795 + 1879617 * 2 ^ 59
def prefixEnd_1879617 : Nat := 4983230072969 + 3 ^ 40 * 1879617 * 2
def baseEnd_1879617 : Nat := 965146967362077723543305

theorem tailTrace_1879617 : CollatzResearch.WordTrace tailWord_1879617 prefixEnd_1879617 965146967362077723543305 := by
  unfold tailWord_1879617
  simp only [CollatzResearch.WordTrace]
  refine ⟨68555264031476096871557105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45703509354317397914371403 68555264031476096871557105)
  ·
    refine ⟨51416448023607072653667829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68555264031476096871557105 51416448023607072653667829)
    ·
      refine ⟨4820292002213163061281359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51416448023607072653667829 4820292002213163061281359)
      ·
        refine ⟨7230438003319744591922039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820292002213163061281359 7230438003319744591922039)
        ·
          refine ⟨10845657004979616887883059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230438003319744591922039 10845657004979616887883059)
          ·
            refine ⟨16268485507469425331824589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10845657004979616887883059 16268485507469425331824589)
            ·
              refine ⟨6100682065301034499434221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16268485507469425331824589 6100682065301034499434221)
              ·
                refine ⟨2287755774487887937287833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6100682065301034499434221 2287755774487887937287833)
                ·
                  refine ⟨1715816830865915952965875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287755774487887937287833 1715816830865915952965875)
                  ·
                    refine ⟨2573725246298873929448813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1715816830865915952965875 2573725246298873929448813)
                    ·
                      refine ⟨965146967362077723543305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573725246298873929448813 965146967362077723543305)
                      ·
                        rfl

theorem cell23_1879617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_1879617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879617 prefixEnd_1879617 := by exact prefixLift 1879617
  have htrace : WordTrace (prefixWord ++ tailWord_1879617) baseStart_1879617 baseEnd_1879617 := by
    simpa [prefixWord, tailWord_1879617, baseEnd_1879617] using wordTrace_append hprefix tailTrace_1879617
  have hstable : (prefixWord ++ tailWord_1879617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879617).length < 2 ^ (prefixWord ++ tailWord_1879617).sum := by decide
  have hdescent : baseEnd_1879617 < baseStart_1879617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879638 : List Nat := [5, 2, 2, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_1879638 : Nat := 118140960795 + 1879638 * 2 ^ 59
def prefixEnd_1879638 : Nat := 4983230072969 + 3 ^ 40 * 1879638 * 2
def baseEnd_1879638 : Nat := 965157750455822141380709

theorem tailTrace_1879638 : CollatzResearch.WordTrace tailWord_1879638 prefixEnd_1879638 965157750455822141380709 := by
  unfold tailWord_1879638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284751872775001091129473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45704019976266678305381045 4284751872775001091129473)
  ·
    refine ⟨3213563904581250818347105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4284751872775001091129473 3213563904581250818347105)
    ·
      refine ⟨2410172928435938113760329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3213563904581250818347105 2410172928435938113760329)
      ·
        refine ⟨1807629696326953585320247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2410172928435938113760329 1807629696326953585320247)
        ·
          refine ⟨2711444544490430377980371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807629696326953585320247 2711444544490430377980371)
          ·
            refine ⟨4067166816735645566970557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711444544490430377980371 4067166816735645566970557)
            ·
              refine ⟨1525187556275867087613959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4067166816735645566970557 1525187556275867087613959)
              ·
                refine ⟨2287781334413800631420939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525187556275867087613959 2287781334413800631420939)
                ·
                  refine ⟨3431672001620700947131409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287781334413800631420939 3431672001620700947131409)
                  ·
                    refine ⟨2573754001215525710348557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3431672001620700947131409 2573754001215525710348557)
                    ·
                      refine ⟨965157750455822141380709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2573754001215525710348557 965157750455822141380709)
                      ·
                        rfl

theorem cell23_1879638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_1879638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879638 prefixEnd_1879638 := by exact prefixLift 1879638
  have htrace : WordTrace (prefixWord ++ tailWord_1879638) baseStart_1879638 baseEnd_1879638 := by
    simpa [prefixWord, tailWord_1879638, baseEnd_1879638] using wordTrace_append hprefix tailTrace_1879638
  have hstable : (prefixWord ++ tailWord_1879638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879638).length < 2 ^ (prefixWord ++ tailWord_1879638).sum := by decide
  have hdescent : baseEnd_1879638 < baseStart_1879638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879657 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 2, 2, 2]
def baseStart_1879657 : Nat := 118140960795 + 1879657 * 2 ^ 59
def prefixEnd_1879657 : Nat := 4983230072969 + 3 ^ 40 * 1879657 * 2
def baseEnd_1879657 : Nat := 965167506588257567043121

theorem tailTrace_1879657 : CollatzResearch.WordTrace tailWord_1879657 prefixEnd_1879657 965167506588257567043121 := by
  unfold tailWord_1879657
  simp only [CollatzResearch.WordTrace]
  refine ⟨68556722951331183703013225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45704481967554122468675483 68556722951331183703013225)
  ·
    refine ⟨51417542213498387777259919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68556722951331183703013225 51417542213498387777259919)
    ·
      refine ⟨77126313320247581665889879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51417542213498387777259919 77126313320247581665889879)
      ·
        refine ⟨115689469980371372498834819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77126313320247581665889879 115689469980371372498834819)
        ·
          refine ⟨173534204970557058748252229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115689469980371372498834819 173534204970557058748252229)
          ·
            refine ⟨32537663431979448515297293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173534204970557058748252229 32537663431979448515297293)
            ·
              refine ⟨12201623786992293193236485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32537663431979448515297293 12201623786992293193236485)
              ·
                refine ⟨2287804460061054973731841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12201623786992293193236485 2287804460061054973731841)
                ·
                  refine ⟨1715853345045791230298881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287804460061054973731841 1715853345045791230298881)
                  ·
                    refine ⟨1286890008784343422724161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715853345045791230298881 1286890008784343422724161)
                    ·
                      refine ⟨965167506588257567043121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286890008784343422724161 965167506588257567043121)
                      ·
                        rfl

theorem cell23_1879657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 2, 2, 2].length) (baseStart_1879657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879657 prefixEnd_1879657 := by exact prefixLift 1879657
  have htrace : WordTrace (prefixWord ++ tailWord_1879657) baseStart_1879657 baseEnd_1879657 := by
    simpa [prefixWord, tailWord_1879657, baseEnd_1879657] using wordTrace_append hprefix tailTrace_1879657
  have hstable : (prefixWord ++ tailWord_1879657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879657).length < 2 ^ (prefixWord ++ tailWord_1879657).sum := by decide
  have hdescent : baseEnd_1879657 < baseStart_1879657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879670 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_1879670 : Nat := 118140960795 + 1879670 * 2 ^ 59
def prefixEnd_1879670 : Nat := 4983230072969 + 3 ^ 40 * 1879670 * 2
def baseEnd_1879670 : Nat := 965174181836766016180561

theorem tailTrace_1879670 : CollatzResearch.WordTrace tailWord_1879670 prefixEnd_1879670 965174181836766016180561 := by
  unfold tailWord_1879670
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284824818767755432702279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45704798066856057948824309 4284824818767755432702279)
  ·
    refine ⟨6427237228151633149053419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4284824818767755432702279 6427237228151633149053419)
    ·
      refine ⟨9640855842227449723580129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6427237228151633149053419 9640855842227449723580129)
      ·
        refine ⟨7230641881670587292685097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9640855842227449723580129 7230641881670587292685097)
        ·
          refine ⟨5422981411252940469513823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7230641881670587292685097 5422981411252940469513823)
          ·
            refine ⟨8134472116879410704270735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5422981411252940469513823 8134472116879410704270735)
            ·
              refine ⟨12201708175319116056406103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8134472116879410704270735 12201708175319116056406103)
              ·
                refine ⟨18302562262978674084609155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12201708175319116056406103 18302562262978674084609155)
                ·
                  refine ⟨27453843394468011126913733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18302562262978674084609155 27453843394468011126913733)
                  ·
                    refine ⟨5147595636462752086296325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27453843394468011126913733 5147595636462752086296325)
                    ·
                      refine ⟨965174181836766016180561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5147595636462752086296325 965174181836766016180561)
                      ·
                        rfl

theorem cell23_1879670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_1879670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879670 prefixEnd_1879670 := by exact prefixLift 1879670
  have htrace : WordTrace (prefixWord ++ tailWord_1879670) baseStart_1879670 baseEnd_1879670 := by
    simpa [prefixWord, tailWord_1879670, baseEnd_1879670] using wordTrace_append hprefix tailTrace_1879670
  have hstable : (prefixWord ++ tailWord_1879670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879670).length < 2 ^ (prefixWord ++ tailWord_1879670).sum := by decide
  have hdescent : baseEnd_1879670 < baseStart_1879670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879708 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1879708 : Nat := 118140960795 + 1879708 * 2 ^ 59
def prefixEnd_1879708 : Nat := 4983230072969 + 3 ^ 40 * 1879708 * 2
def baseEnd_1879708 : Nat := 965193694101636867505387

theorem tailTrace_1879708 : CollatzResearch.WordTrace tailWord_1879708 prefixEnd_1879708 965193694101636867505387 := by
  unfold tailWord_1879708
  simp only [CollatzResearch.WordTrace]
  refine ⟨34279291537073209706559889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45705722049430946275413185 34279291537073209706559889)
  ·
    refine ⟨25709468652804907279919917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34279291537073209706559889 25709468652804907279919917)
    ·
      refine ⟨9641050744801840229969969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25709468652804907279919917 9641050744801840229969969)
      ·
        refine ⟨7230788058601380172477477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9641050744801840229969969 7230788058601380172477477)
        ·
          refine ⟨1355772760987758782339527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7230788058601380172477477 1355772760987758782339527)
          ·
            refine ⟨2033659141481638173509291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355772760987758782339527 2033659141481638173509291)
            ·
              refine ⟨3050488712222457260263937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033659141481638173509291 3050488712222457260263937)
              ·
                refine ⟨2287866534166842945197953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050488712222457260263937 2287866534166842945197953)
                ·
                  refine ⟨1715899900625132208898465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2287866534166842945197953 1715899900625132208898465)
                  ·
                    refine ⟨1286924925468849156673849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1715899900625132208898465 1286924925468849156673849)
                    ·
                      refine ⟨965193694101636867505387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286924925468849156673849 965193694101636867505387)
                      ·
                        rfl

theorem cell23_1879708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1879708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879708 prefixEnd_1879708 := by exact prefixLift 1879708
  have htrace : WordTrace (prefixWord ++ tailWord_1879708) baseStart_1879708 baseEnd_1879708 := by
    simpa [prefixWord, tailWord_1879708, baseEnd_1879708] using wordTrace_append hprefix tailTrace_1879708
  have hstable : (prefixWord ++ tailWord_1879708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879708).length < 2 ^ (prefixWord ++ tailWord_1879708).sum := by decide
  have hdescent : baseEnd_1879708 < baseStart_1879708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879743 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4]
def baseStart_1879743 : Nat := 118140960795 + 1879743 * 2 ^ 59
def prefixEnd_1879743 : Nat := 4983230072969 + 3 ^ 40 * 1879743 * 2
def baseEnd_1879743 : Nat := 965211665924544230567725

theorem tailTrace_1879743 : CollatzResearch.WordTrace tailWord_1879743 prefixEnd_1879743 965211665924544230567725 := by
  unfold tailWord_1879743
  simp only [CollatzResearch.WordTrace]
  refine ⟨68559859629019620390643883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45706573086013080260429255 68559859629019620390643883)
  ·
    refine ⟨102839789443529430585965825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68559859629019620390643883 102839789443529430585965825)
    ·
      refine ⟨77129842082647072939474369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102839789443529430585965825 77129842082647072939474369)
      ·
        refine ⟨57847381561985304704605777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77129842082647072939474369 57847381561985304704605777)
        ·
          refine ⟨43385536171488978528454333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57847381561985304704605777 43385536171488978528454333)
          ·
            refine ⟨16269576064308366948170375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43385536171488978528454333 16269576064308366948170375)
            ·
              refine ⟨24404364096462550422255563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16269576064308366948170375 24404364096462550422255563)
              ·
                refine ⟨36606546144693825633383345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24404364096462550422255563 36606546144693825633383345)
                ·
                  refine ⟨27454909608520369225037509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36606546144693825633383345 27454909608520369225037509)
                  ·
                    refine ⟨5147795551597569229694533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27454909608520369225037509 5147795551597569229694533)
                    ·
                      refine ⟨965211665924544230567725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5147795551597569229694533 965211665924544230567725)
                      ·
                        rfl

theorem cell23_1879743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_1879743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879743 prefixEnd_1879743 := by exact prefixLift 1879743
  have htrace : WordTrace (prefixWord ++ tailWord_1879743) baseStart_1879743 baseEnd_1879743 := by
    simpa [prefixWord, tailWord_1879743, baseEnd_1879743] using wordTrace_append hprefix tailTrace_1879743
  have hstable : (prefixWord ++ tailWord_1879743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879743).length < 2 ^ (prefixWord ++ tailWord_1879743).sum := by decide
  have hdescent : baseEnd_1879743 < baseStart_1879743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879800 : List Nat := [2, 1, 2, 1, 1, 2, 2, 6, 1, 5]
def baseStart_1879800 : Nat := 118140960795 + 1879800 * 2 ^ 59
def prefixEnd_1879800 : Nat := 4983230072969 + 3 ^ 40 * 1879800 * 2
def baseEnd_1879800 : Nat := 321746978107283502518321

theorem tailTrace_1879800 : CollatzResearch.WordTrace tailWord_1879800 prefixEnd_1879800 321746978107283502518321 := by
  unfold tailWord_1879800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34280969294906559562734427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45707959059875412750312569 34280969294906559562734427)
  ·
    refine ⟨51421453942359839344101641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34280969294906559562734427 51421453942359839344101641)
    ·
      refine ⟨38566090456769879508076231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51421453942359839344101641 38566090456769879508076231)
      ·
        refine ⟨57849135685154819262114347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38566090456769879508076231 57849135685154819262114347)
        ·
          refine ⟨86773703527732228893171521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57849135685154819262114347 86773703527732228893171521)
          ·
            refine ⟨65080277645799171669878641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86773703527732228893171521 65080277645799171669878641)
            ·
              refine ⟨48810208234349378752408981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65080277645799171669878641 48810208234349378752408981)
              ·
                refine ⟨2287978510985127129019171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48810208234349378752408981 2287978510985127129019171)
                ·
                  refine ⟨3431967766477690693528757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2287978510985127129019171 3431967766477690693528757)
                  ·
                    refine ⟨321746978107283502518321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3431967766477690693528757 321746978107283502518321)
                    ·
                      rfl

theorem cell23_1879800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_1879800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879800 prefixEnd_1879800 := by exact prefixLift 1879800
  have htrace : WordTrace (prefixWord ++ tailWord_1879800) baseStart_1879800 baseEnd_1879800 := by
    simpa [prefixWord, tailWord_1879800, baseEnd_1879800] using wordTrace_append hprefix tailTrace_1879800
  have hstable : (prefixWord ++ tailWord_1879800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879800).length < 2 ^ (prefixWord ++ tailWord_1879800).sum := by decide
  have hdescent : baseEnd_1879800 < baseStart_1879800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879807 : List Nat := [1, 1, 2, 2, 1, 3, 3, 3, 2, 3, 2]
def baseStart_1879807 : Nat := 118140960795 + 1879807 * 2 ^ 59
def prefixEnd_1879807 : Nat := 4983230072969 + 3 ^ 40 * 1879807 * 2
def baseEnd_1879807 : Nat := 965244528686431980167431

theorem tailTrace_1879807 : CollatzResearch.WordTrace tailWord_1879807 prefixEnd_1879807 965244528686431980167431 := by
  unfold tailWord_1879807
  simp only [CollatzResearch.WordTrace]
  refine ⟨68562193900787759320973675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45708129267191839547315783 68562193900787759320973675)
  ·
    refine ⟨102843290851181638981460513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68562193900787759320973675 102843290851181638981460513)
    ·
      refine ⟨77132468138386229236095385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102843290851181638981460513 77132468138386229236095385)
      ·
        refine ⟨57849351103789671927071539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77132468138386229236095385 57849351103789671927071539)
        ·
          refine ⟨86774026655684507890607309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57849351103789671927071539 86774026655684507890607309)
          ·
            refine ⟨32540259995881690458977741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86774026655684507890607309 32540259995881690458977741)
            ·
              refine ⟨12202597498455633922116653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32540259995881690458977741 12202597498455633922116653)
              ·
                refine ⟨4575974061920862720793745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12202597498455633922116653 4575974061920862720793745)
                ·
                  refine ⟨3431980546440647040595309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4575974061920862720793745 3431980546440647040595309)
                  ·
                    refine ⟨1286992704915242640223241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3431980546440647040595309 1286992704915242640223241)
                    ·
                      refine ⟨965244528686431980167431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1286992704915242640223241 965244528686431980167431)
                      ·
                        rfl

theorem cell23_1879807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 3, 2].length) (baseStart_1879807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879807 prefixEnd_1879807 := by exact prefixLift 1879807
  have htrace : WordTrace (prefixWord ++ tailWord_1879807) baseStart_1879807 baseEnd_1879807 := by
    simpa [prefixWord, tailWord_1879807, baseEnd_1879807] using wordTrace_append hprefix tailTrace_1879807
  have hstable : (prefixWord ++ tailWord_1879807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879807).length < 2 ^ (prefixWord ++ tailWord_1879807).sum := by decide
  have hdescent : baseEnd_1879807 < baseStart_1879807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879831 : List Nat := [1, 1, 3, 4, 2, 2, 1, 4, 1, 1, 3]
def baseStart_1879831 : Nat := 118140960795 + 1879831 * 2 ^ 59
def prefixEnd_1879831 : Nat := 4983230072969 + 3 ^ 40 * 1879831 * 2
def baseEnd_1879831 : Nat := 965256852222139886267321

theorem tailTrace_1879831 : CollatzResearch.WordTrace tailWord_1879831 prefixEnd_1879831 965256852222139886267321 := by
  unfold tailWord_1879831
  simp only [CollatzResearch.WordTrace]
  refine ⟨68563069252700811419847347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45708712835133874279898231 68563069252700811419847347)
  ·
    refine ⟨102844603879051217129771021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68563069252700811419847347 102844603879051217129771021)
    ·
      refine ⟨38566726454644206423664133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102844603879051217129771021 38566726454644206423664133)
      ·
        refine ⟨7231261210245788704437025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38566726454644206423664133 7231261210245788704437025)
        ·
          refine ⟨5423445907684341528327769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7231261210245788704437025 5423445907684341528327769)
          ·
            refine ⟨4067584430763256146245827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5423445907684341528327769 4067584430763256146245827)
            ·
              refine ⟨6101376646144884219368741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4067584430763256146245827 6101376646144884219368741)
              ·
                refine ⟨1144008121152165791131639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6101376646144884219368741 1144008121152165791131639)
                ·
                  refine ⟨1716012181728248686697459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144008121152165791131639 1716012181728248686697459)
                  ·
                    refine ⟨2574018272592373030046189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1716012181728248686697459 2574018272592373030046189)
                    ·
                      refine ⟨965256852222139886267321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2574018272592373030046189 965256852222139886267321)
                      ·
                        rfl

theorem cell23_1879831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_1879831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879831 prefixEnd_1879831 := by exact prefixLift 1879831
  have htrace : WordTrace (prefixWord ++ tailWord_1879831) baseStart_1879831 baseEnd_1879831 := by
    simpa [prefixWord, tailWord_1879831, baseEnd_1879831] using wordTrace_append hprefix tailTrace_1879831
  have hstable : (prefixWord ++ tailWord_1879831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879831).length < 2 ^ (prefixWord ++ tailWord_1879831).sum := by decide
  have hdescent : baseEnd_1879831 < baseStart_1879831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879840 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1879840 : Nat := 118140960795 + 1879840 * 2 ^ 59
def prefixEnd_1879840 : Nat := 4983230072969 + 3 ^ 40 * 1879840 * 2
def baseEnd_1879840 : Nat := 965261473548030351054779

theorem tailTrace_1879840 : CollatzResearch.WordTrace tailWord_1879840 prefixEnd_1879840 965261473548030351054779 := by
  unfold tailWord_1879840
  simp only [CollatzResearch.WordTrace]
  refine ⟨34281698754834102978462487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45708931673112137304616649 34281698754834102978462487)
  ·
    refine ⟨51422548132251154467693731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34281698754834102978462487 51422548132251154467693731)
    ·
      refine ⟨77133822198376731701540597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51422548132251154467693731 77133822198376731701540597)
      ·
        refine ⟨7231295831097818597019431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77133822198376731701540597 7231295831097818597019431)
        ·
          refine ⟨10846943746646727895529147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7231295831097818597019431 10846943746646727895529147)
          ·
            refine ⟨16270415619970091843293721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10846943746646727895529147 16270415619970091843293721)
            ·
              refine ⟨12202811714977568882470291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16270415619970091843293721 12202811714977568882470291)
              ·
                refine ⟨18304217572466353323705437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12202811714977568882470291 18304217572466353323705437)
                ·
                  refine ⟨6864081589674882496389539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18304217572466353323705437 6864081589674882496389539)
                  ·
                    refine ⟨10296122384512323744584309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6864081589674882496389539 10296122384512323744584309)
                    ·
                      refine ⟨965261473548030351054779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10296122384512323744584309 965261473548030351054779)
                      ·
                        rfl

theorem cell23_1879840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1879840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879840 prefixEnd_1879840 := by exact prefixLift 1879840
  have htrace : WordTrace (prefixWord ++ tailWord_1879840) baseStart_1879840 baseEnd_1879840 := by
    simpa [prefixWord, tailWord_1879840, baseEnd_1879840] using wordTrace_append hprefix tailTrace_1879840
  have hstable : (prefixWord ++ tailWord_1879840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879840).length < 2 ^ (prefixWord ++ tailWord_1879840).sum := by decide
  have hdescent : baseEnd_1879840 < baseStart_1879840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879857 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 3]
def baseStart_1879857 : Nat := 118140960795 + 1879857 * 2 ^ 59
def prefixEnd_1879857 : Nat := 4983230072969 + 3 ^ 40 * 1879857 * 2
def baseEnd_1879857 : Nat := 965270202719156784542201

theorem tailTrace_1879857 : CollatzResearch.WordTrace tailWord_1879857 prefixEnd_1879857 965270202719156784542201 := by
  unfold tailWord_1879857
  simp only [CollatzResearch.WordTrace]
  refine ⟨68564017550606617860293825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45709345033737745240195883 68564017550606617860293825)
  ·
    refine ⟨51423013162954963395220369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68564017550606617860293825 51423013162954963395220369)
    ·
      refine ⟨38567259872216222546415277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51423013162954963395220369 38567259872216222546415277)
      ·
        refine ⟨14462722452081083454905729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38567259872216222546415277 14462722452081083454905729)
        ·
          refine ⟨10847041839060812591179297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14462722452081083454905729 10847041839060812591179297)
          ·
            refine ⟨8135281379295609443384473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10847041839060812591179297 8135281379295609443384473)
            ·
              refine ⟨6101461034471707082538355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8135281379295609443384473 6101461034471707082538355)
              ·
                refine ⟨9152191551707560623807533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6101461034471707082538355 9152191551707560623807533)
                ·
                  refine ⟨3432071831890335233927825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9152191551707560623807533 3432071831890335233927825)
                  ·
                    refine ⟨2574053873917751425445869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3432071831890335233927825 2574053873917751425445869)
                    ·
                      refine ⟨965270202719156784542201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2574053873917751425445869 965270202719156784542201)
                      ·
                        rfl

theorem cell23_1879857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_1879857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879857 prefixEnd_1879857 := by exact prefixLift 1879857
  have htrace : WordTrace (prefixWord ++ tailWord_1879857) baseStart_1879857 baseEnd_1879857 := by
    simpa [prefixWord, tailWord_1879857, baseEnd_1879857] using wordTrace_append hprefix tailTrace_1879857
  have hstable : (prefixWord ++ tailWord_1879857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879857).length < 2 ^ (prefixWord ++ tailWord_1879857).sum := by decide
  have hdescent : baseEnd_1879857 < baseStart_1879857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879871 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 1, 1, 4]
def baseStart_1879871 : Nat := 118140960795 + 1879871 * 2 ^ 59
def prefixEnd_1879871 : Nat := 4983230072969 + 3 ^ 40 * 1879871 * 2
def baseEnd_1879871 : Nat := 965277391448319729767137

theorem tailTrace_1879871 : CollatzResearch.WordTrace tailWord_1879871 prefixEnd_1879871 965277391448319729767137 := by
  unfold tailWord_1879871
  simp only [CollatzResearch.WordTrace]
  refine ⟨68564528172555898251303467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45709685448370598834202311 68564528172555898251303467)
  ·
    refine ⟨102846792258833847376955201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68564528172555898251303467 102846792258833847376955201)
    ·
      refine ⟨77135094194125385532716401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102846792258833847376955201 77135094194125385532716401)
      ·
        refine ⟨57851320645594039149537301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77135094194125385532716401 57851320645594039149537301)
        ·
          refine ⟨2711780655262220585134561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57851320645594039149537301 2711780655262220585134561)
          ·
            refine ⟨2033835491446665438850921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711780655262220585134561 2033835491446665438850921)
            ·
              refine ⟨1525376618584999079138191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2033835491446665438850921 1525376618584999079138191)
              ·
                refine ⟨2288064927877498618707287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525376618584999079138191 2288064927877498618707287)
                ·
                  refine ⟨3432097391816247928060931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2288064927877498618707287 3432097391816247928060931)
                  ·
                    refine ⟨5148146087724371892091397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3432097391816247928060931 5148146087724371892091397)
                    ·
                      refine ⟨965277391448319729767137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5148146087724371892091397 965277391448319729767137)
                      ·
                        rfl

theorem cell23_1879871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 1, 1, 4].length) (baseStart_1879871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879871 prefixEnd_1879871 := by exact prefixLift 1879871
  have htrace : WordTrace (prefixWord ++ tailWord_1879871) baseStart_1879871 baseEnd_1879871 := by
    simpa [prefixWord, tailWord_1879871, baseEnd_1879871] using wordTrace_append hprefix tailTrace_1879871
  have hstable : (prefixWord ++ tailWord_1879871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879871).length < 2 ^ (prefixWord ++ tailWord_1879871).sum := by decide
  have hdescent : baseEnd_1879871 < baseStart_1879871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879904 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3]
def baseStart_1879904 : Nat := 118140960795 + 1879904 * 2 ^ 59
def prefixEnd_1879904 : Nat := 4983230072969 + 3 ^ 40 * 1879904 * 2
def baseEnd_1879904 : Nat := 965294336309918100654485

theorem tailTrace_1879904 : CollatzResearch.WordTrace tailWord_1879904 prefixEnd_1879904 965294336309918100654485 := by
  unfold tailWord_1879904
  simp only [CollatzResearch.WordTrace]
  refine ⟨34282865890718172443627383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45710487854290896591503177 34282865890718172443627383)
  ·
    refine ⟨51424298836077258665441075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34282865890718172443627383 51424298836077258665441075)
    ·
      refine ⟨77136448254115887998161613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51424298836077258665441075 77136448254115887998161613)
      ·
        refine ⟨28926168095293457999310605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77136448254115887998161613 28926168095293457999310605)
        ·
          refine ⟨10847313035735046749741477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28926168095293457999310605 10847313035735046749741477)
          ·
            refine ⟨2033871194200321265576527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10847313035735046749741477 2033871194200321265576527)
            ·
              refine ⟨3050806791300481898364791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033871194200321265576527 3050806791300481898364791)
              ·
                refine ⟨4576210186950722847547187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3050806791300481898364791 4576210186950722847547187)
                ·
                  refine ⟨6864315280426084271320781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576210186950722847547187 6864315280426084271320781)
                  ·
                    refine ⟨2574118230159781601745293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6864315280426084271320781 2574118230159781601745293)
                    ·
                      refine ⟨965294336309918100654485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2574118230159781601745293 965294336309918100654485)
                      ·
                        rfl

theorem cell23_1879904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 3].length) (baseStart_1879904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879904 prefixEnd_1879904 := by exact prefixLift 1879904
  have htrace : WordTrace (prefixWord ++ tailWord_1879904) baseStart_1879904 baseEnd_1879904 := by
    simpa [prefixWord, tailWord_1879904, baseEnd_1879904] using wordTrace_append hprefix tailTrace_1879904
  have hstable : (prefixWord ++ tailWord_1879904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879904).length < 2 ^ (prefixWord ++ tailWord_1879904).sum := by decide
  have hdescent : baseEnd_1879904 < baseStart_1879904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1879930 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_1879930 : Nat := 118140960795 + 1879930 * 2 ^ 59
def prefixEnd_1879930 : Nat := 4983230072969 + 3 ^ 40 * 1879930 * 2
def baseEnd_1879930 : Nat := 965307686806934998929365

theorem tailTrace_1879930 : CollatzResearch.WordTrace tailWord_1879930 prefixEnd_1879930 965307686806934998929365 := by
  unfold tailWord_1879930
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141670019835537831925311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45711120052894767551800829 17141670019835537831925311)
  ·
    refine ⟨25712505029753306747887967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17141670019835537831925311 25712505029753306747887967)
    ·
      refine ⟨38568757544629960121831951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25712505029753306747887967 38568757544629960121831951)
      ·
        refine ⟨57853136316944940182747927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38568757544629960121831951 57853136316944940182747927)
        ·
          refine ⟨86779704475417410274121891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57853136316944940182747927 86779704475417410274121891)
          ·
            refine ⟨130169556713126115411182837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86779704475417410274121891 130169556713126115411182837)
            ·
              refine ⟨12203395941855573319798391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130169556713126115411182837 12203395941855573319798391)
              ·
                refine ⟨18305093912783359979697587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12203395941855573319798391 18305093912783359979697587)
                ·
                  refine ⟨27457640869175039969546381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18305093912783359979697587 27457640869175039969546381)
                  ·
                    refine ⟨10296615325940639988579893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27457640869175039969546381 10296615325940639988579893)
                    ·
                      refine ⟨965307686806934998929365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10296615325940639988579893 965307686806934998929365)
                      ·
                        rfl

theorem cell23_1879930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_1879930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1879930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1879930 prefixEnd_1879930 := by exact prefixLift 1879930
  have htrace : WordTrace (prefixWord ++ tailWord_1879930) baseStart_1879930 baseEnd_1879930 := by
    simpa [prefixWord, tailWord_1879930, baseEnd_1879930] using wordTrace_append hprefix tailTrace_1879930
  have hstable : (prefixWord ++ tailWord_1879930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1879930).length < 2 ^ (prefixWord ++ tailWord_1879930).sum := by decide
  have hdescent : baseEnd_1879930 < baseStart_1879930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1879930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880057 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 8]
def baseStart_1880057 : Nat := 118140960795 + 1880057 * 2 ^ 59
def prefixEnd_1880057 : Nat := 4983230072969 + 3 ^ 40 * 1880057 * 2
def baseEnd_1880057 : Nat := 107263655427784000226809

theorem tailTrace_1880057 : CollatzResearch.WordTrace tailWord_1880057 prefixEnd_1880057 107263655427784000226809 := by
  unfold tailWord_1880057
  simp only [CollatzResearch.WordTrace]
  refine ⟨68571312149882052017574425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45714208099921368011716283 68571312149882052017574425)
  ·
    refine ⟨51428484112411539013180819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68571312149882052017574425 51428484112411539013180819)
    ·
      refine ⟨77142726168617308519771229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51428484112411539013180819 77142726168617308519771229)
      ·
        refine ⟨28928522313231490694914211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77142726168617308519771229 28928522313231490694914211)
        ·
          refine ⟨43392783469847236042371317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28928522313231490694914211 43392783469847236042371317)
          ·
            refine ⟨4068073450298178378972311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43392783469847236042371317 4068073450298178378972311)
            ·
              refine ⟨6102110175447267568458467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068073450298178378972311 6102110175447267568458467)
              ·
                refine ⟨9153165263170901352687701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102110175447267568458467 9153165263170901352687701)
                ·
                  refine ⟨107263655427784000226809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 9153165263170901352687701 107263655427784000226809)
                  ·
                    rfl

theorem cell23_1880057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 8].length) (baseStart_1880057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880057 prefixEnd_1880057 := by exact prefixLift 1880057
  have htrace : WordTrace (prefixWord ++ tailWord_1880057) baseStart_1880057 baseEnd_1880057 := by
    simpa [prefixWord, tailWord_1880057, baseEnd_1880057] using wordTrace_append hprefix tailTrace_1880057
  have hstable : (prefixWord ++ tailWord_1880057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880057).length < 2 ^ (prefixWord ++ tailWord_1880057).sum := by decide
  have hdescent : baseEnd_1880057 < baseStart_1880057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880061 : List Nat := [1, 4, 1, 1, 1, 2, 4, 4, 1, 4]
def baseStart_1880061 : Nat := 118140960795 + 1880061 * 2 ^ 59
def prefixEnd_1880061 : Nat := 4983230072969 + 3 ^ 40 * 1880061 * 2
def baseEnd_1880061 : Nat := 321791650924224662130421

theorem tailTrace_1880061 : CollatzResearch.WordTrace tailWord_1880061 prefixEnd_1880061 321791650924224662130421 := by
  unfold tailWord_1880061
  simp only [CollatzResearch.WordTrace]
  refine ⟨68571458041867560700720037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45714305361245040467146691 68571458041867560700720037)
  ·
    refine ⟨12857148382850167631385007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68571458041867560700720037 12857148382850167631385007)
    ·
      refine ⟨19285722574275251447077511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12857148382850167631385007 19285722574275251447077511)
      ·
        refine ⟨28928583861412877170616267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19285722574275251447077511 28928583861412877170616267)
        ·
          refine ⟨43392875792119315755924401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28928583861412877170616267 43392875792119315755924401)
          ·
            refine ⟨32544656844089486816943301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43392875792119315755924401 32544656844089486816943301)
            ·
              refine ⟨6102123158266778778176869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32544656844089486816943301 6102123158266778778176869)
              ·
                refine ⟨1144148092175021020908163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6102123158266778778176869 1144148092175021020908163)
                ·
                  refine ⟨1716222138262531531362245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144148092175021020908163 1716222138262531531362245)
                  ·
                    refine ⟨321791650924224662130421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1716222138262531531362245 321791650924224662130421)
                    ·
                      rfl

theorem cell23_1880061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_1880061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880061 prefixEnd_1880061 := by exact prefixLift 1880061
  have htrace : WordTrace (prefixWord ++ tailWord_1880061) baseStart_1880061 baseEnd_1880061 := by
    simpa [prefixWord, tailWord_1880061, baseEnd_1880061] using wordTrace_append hprefix tailTrace_1880061
  have hstable : (prefixWord ++ tailWord_1880061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880061).length < 2 ^ (prefixWord ++ tailWord_1880061).sum := by decide
  have hdescent : baseEnd_1880061 < baseStart_1880061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880124 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_1880124 : Nat := 118140960795 + 1880124 * 2 ^ 59
def prefixEnd_1880124 : Nat := 4983230072969 + 3 ^ 40 * 1880124 * 2
def baseEnd_1880124 : Nat := 965407302053907239903473

theorem tailTrace_1880124 : CollatzResearch.WordTrace tailWord_1880124 prefixEnd_1880124 965407302053907239903473 := by
  unfold tailWord_1880124
  simp only [CollatzResearch.WordTrace]
  refine ⟨34286877920319661230131713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45715837227092881640175617 34286877920319661230131713)
  ·
    refine ⟨25715158440239745922598785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34286877920319661230131713 25715158440239745922598785)
    ·
      refine ⟨19286368830179809441949089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25715158440239745922598785 19286368830179809441949089)
      ·
        refine ⟨14464776622634857081461817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19286368830179809441949089 14464776622634857081461817)
        ·
          refine ⟨10848582466976142811096363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14464776622634857081461817 10848582466976142811096363)
          ·
            refine ⟨16272873700464214216644545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848582466976142811096363 16272873700464214216644545)
            ·
              refine ⟨12204655275348160662483409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16272873700464214216644545 12204655275348160662483409)
              ·
                refine ⟨9153491456511120496862557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12204655275348160662483409 9153491456511120496862557)
                ·
                  refine ⟨3432559296191670186323459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9153491456511120496862557 3432559296191670186323459)
                  ·
                    refine ⟨5148838944287505279485189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3432559296191670186323459 5148838944287505279485189)
                    ·
                      refine ⟨965407302053907239903473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5148838944287505279485189 965407302053907239903473)
                      ·
                        rfl

theorem cell23_1880124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_1880124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880124 prefixEnd_1880124 := by exact prefixLift 1880124
  have htrace : WordTrace (prefixWord ++ tailWord_1880124) baseStart_1880124 baseEnd_1880124 := by
    simpa [prefixWord, tailWord_1880124, baseEnd_1880124] using wordTrace_append hprefix tailTrace_1880124
  have hstable : (prefixWord ++ tailWord_1880124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880124).length < 2 ^ (prefixWord ++ tailWord_1880124).sum := by decide
  have hdescent : baseEnd_1880124 < baseStart_1880124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880137 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1880137 : Nat := 118140960795 + 1880137 * 2 ^ 59
def prefixEnd_1880137 : Nat := 4983230072969 + 3 ^ 40 * 1880137 * 2
def baseEnd_1880137 : Nat := 965413977302415689040913

theorem tailTrace_1880137 : CollatzResearch.WordTrace tailWord_1880137 prefixEnd_1880137 965413977302415689040913 := by
  unfold tailWord_1880137
  simp only [CollatzResearch.WordTrace]
  refine ⟨68574229989592225680486665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45716153326394817120324443 68574229989592225680486665)
  ·
    refine ⟨51430672492194169260364999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68574229989592225680486665 51430672492194169260364999)
    ·
      refine ⟨77146008738291253890547499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51430672492194169260364999 77146008738291253890547499)
      ·
        refine ⟨115719013107436880835821249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77146008738291253890547499 115719013107436880835821249)
        ·
          refine ⟨86789259830577660626865937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115719013107436880835821249 86789259830577660626865937)
          ·
            refine ⟨65091944872933245470149453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86789259830577660626865937 65091944872933245470149453)
            ·
              refine ⟨24409479327349967051306045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65091944872933245470149453 24409479327349967051306045)
              ·
                refine ⟨9153554747756237644239767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24409479327349967051306045 9153554747756237644239767)
                ·
                  refine ⟨13730332121634356466359651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9153554747756237644239767 13730332121634356466359651)
                  ·
                    refine ⟨20595498182451534699539477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13730332121634356466359651 20595498182451534699539477)
                    ·
                      refine ⟨965413977302415689040913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20595498182451534699539477 965413977302415689040913)
                      ·
                        rfl

theorem cell23_1880137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1880137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880137 prefixEnd_1880137 := by exact prefixLift 1880137
  have htrace : WordTrace (prefixWord ++ tailWord_1880137) baseStart_1880137 baseEnd_1880137 := by
    simpa [prefixWord, tailWord_1880137, baseEnd_1880137] using wordTrace_append hprefix tailTrace_1880137
  have hstable : (prefixWord ++ tailWord_1880137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880137).length < 2 ^ (prefixWord ++ tailWord_1880137).sum := by decide
  have hdescent : baseEnd_1880137 < baseStart_1880137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880141 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1880141 : Nat := 118140960795 + 1880141 * 2 ^ 59
def prefixEnd_1880141 : Nat := 4983230072969 + 3 ^ 40 * 1880141 * 2
def baseEnd_1880141 : Nat := 965416031225033673390895

theorem tailTrace_1880141 : CollatzResearch.WordTrace tailWord_1880141 prefixEnd_1880141 965416031225033673390895 := by
  unfold tailWord_1880141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68574375881577734363632277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45716250587718489575754851 68574375881577734363632277)
  ·
    refine ⟨3214423869448956298295263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68574375881577734363632277 3214423869448956298295263)
    ·
      refine ⟨4821635804173434447442895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214423869448956298295263 4821635804173434447442895)
      ·
        refine ⟨7232453706260151671164343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821635804173434447442895 7232453706260151671164343)
        ·
          refine ⟨10848680559390227506746515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232453706260151671164343 10848680559390227506746515)
          ·
            refine ⟨16273020839085341260119773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10848680559390227506746515 16273020839085341260119773)
            ·
              refine ⟨6102382814657002972544915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16273020839085341260119773 6102382814657002972544915)
              ·
                refine ⟨9153574221985504458817373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6102382814657002972544915 9153574221985504458817373)
                ·
                  refine ⟨3432590333244564172056515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9153574221985504458817373 3432590333244564172056515)
                  ·
                    refine ⟨5148885499866846258084773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3432590333244564172056515 5148885499866846258084773)
                    ·
                      refine ⟨965416031225033673390895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5148885499866846258084773 965416031225033673390895)
                      ·
                        rfl

theorem cell23_1880141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1880141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880141 prefixEnd_1880141 := by exact prefixLift 1880141
  have htrace : WordTrace (prefixWord ++ tailWord_1880141) baseStart_1880141 baseEnd_1880141 := by
    simpa [prefixWord, tailWord_1880141, baseEnd_1880141] using wordTrace_append hprefix tailTrace_1880141
  have hstable : (prefixWord ++ tailWord_1880141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880141).length < 2 ^ (prefixWord ++ tailWord_1880141).sum := by decide
  have hdescent : baseEnd_1880141 < baseStart_1880141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880154 : List Nat := [3, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_1880154 : Nat := 118140960795 + 1880154 * 2 ^ 59
def prefixEnd_1880154 : Nat := 4983230072969 + 3 ^ 40 * 1880154 * 2
def baseEnd_1880154 : Nat := 965422706473542122528335

theorem tailTrace_1880154 : CollatzResearch.WordTrace tailWord_1880154 prefixEnd_1880154 965422706473542122528335 := by
  unfold tailWord_1880154
  simp only [CollatzResearch.WordTrace]
  refine ⟨17143712507632659395963879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45716566687020425055903677 17143712507632659395963879)
  ·
    refine ⟨25715568761448989093945819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17143712507632659395963879 25715568761448989093945819)
    ·
      refine ⟨38573353142173483640918729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25715568761448989093945819 38573353142173483640918729)
      ·
        refine ⟨28930014856630112730689047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38573353142173483640918729 28930014856630112730689047)
        ·
          refine ⟨43395022284945169096033571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28930014856630112730689047 43395022284945169096033571)
          ·
            refine ⟨65092533427417753644050357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43395022284945169096033571 65092533427417753644050357)
            ·
              refine ⟨6102425008820414404129721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65092533427417753644050357 6102425008820414404129721)
              ·
                refine ⟨4576818756615310803097291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6102425008820414404129721 4576818756615310803097291)
                ·
                  refine ⟨6865228134922966204645937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4576818756615310803097291 6865228134922966204645937)
                  ·
                    refine ⟨5148921101192224653484453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6865228134922966204645937 5148921101192224653484453)
                    ·
                      refine ⟨965422706473542122528335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5148921101192224653484453 965422706473542122528335)
                      ·
                        rfl

theorem cell23_1880154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_1880154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880154 prefixEnd_1880154 := by exact prefixLift 1880154
  have htrace : WordTrace (prefixWord ++ tailWord_1880154) baseStart_1880154 baseEnd_1880154 := by
    simpa [prefixWord, tailWord_1880154, baseEnd_1880154] using wordTrace_append hprefix tailTrace_1880154
  have hstable : (prefixWord ++ tailWord_1880154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880154).length < 2 ^ (prefixWord ++ tailWord_1880154).sum := by decide
  have hdescent : baseEnd_1880154 < baseStart_1880154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880175 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 1, 2, 2]
def baseStart_1880175 : Nat := 118140960795 + 1880175 * 2 ^ 59
def prefixEnd_1880175 : Nat := 4983230072969 + 3 ^ 40 * 1880175 * 2
def baseEnd_1880175 : Nat := 965433489567286540365739

theorem tailTrace_1880175 : CollatzResearch.WordTrace tailWord_1880175 prefixEnd_1880175 965433489567286540365739 := by
  unfold tailWord_1880175
  simp only [CollatzResearch.WordTrace]
  refine ⟨68575615963454558170369979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45717077308969705446913319 68575615963454558170369979)
  ·
    refine ⟨102863423945181837255554969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68575615963454558170369979 102863423945181837255554969)
    ·
      refine ⟨77147567958886377941666227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102863423945181837255554969 77147567958886377941666227)
      ·
        refine ⟨115721351938329566912499341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77147567958886377941666227 115721351938329566912499341)
        ·
          refine ⟨43395506976873587592187253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115721351938329566912499341 43395506976873587592187253)
          ·
            refine ⟨4068328779081898836767555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43395506976873587592187253 4068328779081898836767555)
            ·
              refine ⟨6102493168622848255151333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4068328779081898836767555 6102493168622848255151333)
              ·
                refine ⟨1144217469116784047840875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6102493168622848255151333 1144217469116784047840875)
                ·
                  refine ⟨1716326203675176071761313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1144217469116784047840875 1716326203675176071761313)
                  ·
                    refine ⟨1287244652756382053820985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1716326203675176071761313 1287244652756382053820985)
                    ·
                      refine ⟨965433489567286540365739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287244652756382053820985 965433489567286540365739)
                      ·
                        rfl

theorem cell23_1880175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 1, 2, 2].length) (baseStart_1880175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880175 prefixEnd_1880175 := by exact prefixLift 1880175
  have htrace : WordTrace (prefixWord ++ tailWord_1880175) baseStart_1880175 baseEnd_1880175 := by
    simpa [prefixWord, tailWord_1880175, baseEnd_1880175] using wordTrace_append hprefix tailTrace_1880175
  have hstable : (prefixWord ++ tailWord_1880175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880175).length < 2 ^ (prefixWord ++ tailWord_1880175).sum := by decide
  have hdescent : baseEnd_1880175 < baseStart_1880175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880177 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 1, 9]
def baseStart_1880177 : Nat := 118140960795 + 1880177 * 2 ^ 59
def prefixEnd_1880177 : Nat := 4983230072969 + 3 ^ 40 * 1880177 * 2
def baseEnd_1880177 : Nat := 321811505509531844180243

theorem tailTrace_1880177 : CollatzResearch.WordTrace tailWord_1880177 prefixEnd_1880177 321811505509531844180243 := by
  unfold tailWord_1880177
  simp only [CollatzResearch.WordTrace]
  refine ⟨68575688909447312511942785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45717125939631541674628523 68575688909447312511942785)
  ·
    refine ⟨51431766682085484383957089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68575688909447312511942785 51431766682085484383957089)
    ·
      refine ⟨38573825011564113287967817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51431766682085484383957089 38573825011564113287967817)
      ·
        refine ⟨28930368758673084965975863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38573825011564113287967817 28930368758673084965975863)
        ·
          refine ⟨43395553138009627448963795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28930368758673084965975863 43395553138009627448963795)
          ·
            refine ⟨65093329707014441173445693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43395553138009627448963795 65093329707014441173445693)
            ·
              refine ⟨24409998640130415440042135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65093329707014441173445693 24409998640130415440042135)
              ·
                refine ⟨36614997960195623160063203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24409998640130415440042135 36614997960195623160063203)
                ·
                  refine ⟨54922496940293434740094805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36614997960195623160063203 54922496940293434740094805)
                  ·
                    refine ⟨321811505509531844180243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 54922496940293434740094805 321811505509531844180243)
                    ·
                      rfl

theorem cell23_1880177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_1880177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880177 prefixEnd_1880177 := by exact prefixLift 1880177
  have htrace : WordTrace (prefixWord ++ tailWord_1880177) baseStart_1880177 baseEnd_1880177 := by
    simpa [prefixWord, tailWord_1880177, baseEnd_1880177] using wordTrace_append hprefix tailTrace_1880177
  have hstable : (prefixWord ++ tailWord_1880177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880177).length < 2 ^ (prefixWord ++ tailWord_1880177).sum := by decide
  have hdescent : baseEnd_1880177 < baseStart_1880177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880187 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5]
def baseStart_1880187 : Nat := 118140960795 + 1880187 * 2 ^ 59
def prefixEnd_1880187 : Nat := 4983230072969 + 3 ^ 40 * 1880187 * 2
def baseEnd_1880187 : Nat := 965439651335140493415683

theorem tailTrace_1880187 : CollatzResearch.WordTrace tailWord_1880187 prefixEnd_1880187 965439651335140493415683 := by
  unfold tailWord_1880187
  simp only [CollatzResearch.WordTrace]
  refine ⟨68576053639411084219806815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45717369092940722813204543 68576053639411084219806815)
  ·
    refine ⟨102864080459116626329710223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68576053639411084219806815 102864080459116626329710223)
    ·
      refine ⟨154296120688674939494565335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102864080459116626329710223 154296120688674939494565335)
      ·
        refine ⟨231444181033012409241848003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154296120688674939494565335 231444181033012409241848003)
        ·
          refine ⟨347166271549518613862772005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231444181033012409241848003 347166271549518613862772005)
          ·
            refine ⟨65093675915534740099269751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347166271549518613862772005 65093675915534740099269751)
            ·
              refine ⟨97640513873302110148904627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65093675915534740099269751 97640513873302110148904627)
              ·
                refine ⟨146460770809953165223356941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97640513873302110148904627 146460770809953165223356941)
                ·
                  refine ⟨54922789053732436958758853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146460770809953165223356941 54922789053732436958758853)
                  ·
                    refine ⟨10298022947574831929767285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54922789053732436958758853 10298022947574831929767285)
                    ·
                      refine ⟨965439651335140493415683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10298022947574831929767285 965439651335140493415683)
                      ·
                        rfl

theorem cell23_1880187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 5].length) (baseStart_1880187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880187 prefixEnd_1880187 := by exact prefixLift 1880187
  have htrace : WordTrace (prefixWord ++ tailWord_1880187) baseStart_1880187 baseEnd_1880187 := by
    simpa [prefixWord, tailWord_1880187, baseEnd_1880187] using wordTrace_append hprefix tailTrace_1880187
  have hstable : (prefixWord ++ tailWord_1880187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880187).length < 2 ^ (prefixWord ++ tailWord_1880187).sum := by decide
  have hdescent : baseEnd_1880187 < baseStart_1880187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880201 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 3, 3, 2]
def baseStart_1880201 : Nat := 118140960795 + 1880201 * 2 ^ 59
def prefixEnd_1880201 : Nat := 4983230072969 + 3 ^ 40 * 1880201 * 2
def baseEnd_1880201 : Nat := 965446840064303438640619

theorem tailTrace_1880201 : CollatzResearch.WordTrace tailWord_1880201 prefixEnd_1880201 965446840064303438640619 := by
  unfold tailWord_1880201
  simp only [CollatzResearch.WordTrace]
  refine ⟨68576564261360364610816457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45717709507573576407210971 68576564261360364610816457)
  ·
    refine ⟨51432423196020273458112343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68576564261360364610816457 51432423196020273458112343)
    ·
      refine ⟨77148634794030410187168515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51432423196020273458112343 77148634794030410187168515)
      ·
        refine ⟨115722952191045615280752773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77148634794030410187168515 115722952191045615280752773)
        ·
          refine ⟨21698053535821052865141145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115722952191045615280752773 21698053535821052865141145)
          ·
            refine ⟨16273540151865789648855859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21698053535821052865141145 16273540151865789648855859)
            ·
              refine ⟨24410310227798684473283789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16273540151865789648855859 24410310227798684473283789)
              ·
                refine ⟨9153866335424506677481421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24410310227798684473283789 9153866335424506677481421)
                ·
                  refine ⟨3432699875784190004055533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9153866335424506677481421 3432699875784190004055533)
                  ·
                    refine ⟨1287262453419071251520825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3432699875784190004055533 1287262453419071251520825)
                    ·
                      refine ⟨965446840064303438640619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1287262453419071251520825 965446840064303438640619)
                      ·
                        rfl

theorem cell23_1880201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 3, 3, 2].length) (baseStart_1880201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880201 prefixEnd_1880201 := by exact prefixLift 1880201
  have htrace : WordTrace (prefixWord ++ tailWord_1880201) baseStart_1880201 baseEnd_1880201 := by
    simpa [prefixWord, tailWord_1880201, baseEnd_1880201] using wordTrace_append hprefix tailTrace_1880201
  have hstable : (prefixWord ++ tailWord_1880201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880201).length < 2 ^ (prefixWord ++ tailWord_1880201).sum := by decide
  have hdescent : baseEnd_1880201 < baseStart_1880201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1880224 : List Nat := [2, 1, 1, 4, 2, 2, 1, 2, 2, 6]
def baseStart_1880224 : Nat := 118140960795 + 1880224 * 2 ^ 59
def prefixEnd_1880224 : Nat := 4983230072969 + 3 ^ 40 * 1880224 * 2
def baseEnd_1880224 : Nat := 321819550039785616217671

theorem tailTrace_1880224 : CollatzResearch.WordTrace tailWord_1880224 prefixEnd_1880224 321819550039785616217671 := by
  unfold tailWord_1880224
  simp only [CollatzResearch.WordTrace]
  refine ⟨34288701570138519769451863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45718268760184693025935817 34288701570138519769451863)
  ·
    refine ⟨51433052355207779654177795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34288701570138519769451863 51433052355207779654177795)
    ·
      refine ⟨77149578532811669481266693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51433052355207779654177795 77149578532811669481266693)
      ·
        refine ⟨14465545974902188027737505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77149578532811669481266693 14465545974902188027737505)
        ·
          refine ⟨10849159481176641020803129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14465545974902188027737505 10849159481176641020803129)
          ·
            refine ⟨8136869610882480765602347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10849159481176641020803129 8136869610882480765602347)
            ·
              refine ⟨12205304416323721148403521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8136869610882480765602347 12205304416323721148403521)
              ·
                refine ⟨9153978312242790861302641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12205304416323721148403521 9153978312242790861302641)
                ·
                  refine ⟨6865483734182093145976981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9153978312242790861302641 6865483734182093145976981)
                  ·
                    refine ⟨321819550039785616217671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6865483734182093145976981 321819550039785616217671)
                    ·
                      rfl

theorem cell23_1880224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 2, 2, 6].length) (baseStart_1880224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1880224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1880224 prefixEnd_1880224 := by exact prefixLift 1880224
  have htrace : WordTrace (prefixWord ++ tailWord_1880224) baseStart_1880224 baseEnd_1880224 := by
    simpa [prefixWord, tailWord_1880224, baseEnd_1880224] using wordTrace_append hprefix tailTrace_1880224
  have hstable : (prefixWord ++ tailWord_1880224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1880224).length < 2 ^ (prefixWord ++ tailWord_1880224).sum := by decide
  have hdescent : baseEnd_1880224 < baseStart_1880224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1880224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
