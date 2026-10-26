import V185TrunkScan23Chunk0822

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4869096 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_4869096 : Nat := 118140960795 + 4869096 * 2 ^ 59
def prefixEnd_4869096 : Nat := 4983230072969 + 3 ^ 40 * 4869096 * 2
def baseEnd_4869096 : Nat := 2500186600884386873207441

theorem tailTrace_4869096 : CollatzResearch.WordTrace tailWord_4869096 prefixEnd_4869096 2500186600884386873207441 := by
  unfold tailWord_4869096
  simp only [CollatzResearch.WordTrace]
  refine ⟨88795260384052121118405571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118393680512069494824540761 88795260384052121118405571)
  ·
    refine ⟨133192890576078181677608357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88795260384052121118405571 133192890576078181677608357)
    ·
      refine ⟨24973666983014659064551567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133192890576078181677608357 24973666983014659064551567)
      ·
        refine ⟨37460500474521988596827351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24973666983014659064551567 37460500474521988596827351)
        ·
          refine ⟨56190750711782982895241027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37460500474521988596827351 56190750711782982895241027)
          ·
            refine ⟨84286126067674474342861541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56190750711782982895241027 84286126067674474342861541)
            ·
              refine ⟨15803648637688963939286539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84286126067674474342861541 15803648637688963939286539)
              ·
                refine ⟨23705472956533445908929809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15803648637688963939286539 23705472956533445908929809)
                ·
                  refine ⟨17779104717400084431697357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23705472956533445908929809 17779104717400084431697357)
                  ·
                    refine ⟨6667164269025031661886509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17779104717400084431697357 6667164269025031661886509)
                    ·
                      refine ⟨2500186600884386873207441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6667164269025031661886509 2500186600884386873207441)
                      ·
                        rfl

theorem cell23_4869096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_4869096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869096 prefixEnd_4869096 := by exact prefixLift 4869096
  have htrace : WordTrace (prefixWord ++ tailWord_4869096) baseStart_4869096 baseEnd_4869096 := by
    simpa [prefixWord, tailWord_4869096, baseEnd_4869096] using wordTrace_append hprefix tailTrace_4869096
  have hstable : (prefixWord ++ tailWord_4869096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869096).length < 2 ^ (prefixWord ++ tailWord_4869096).sum := by decide
  have hdescent : baseEnd_4869096 < baseStart_4869096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869197 : List Nat := [1, 6, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4869197 : Nat := 118140960795 + 4869197 * 2 ^ 59
def prefixEnd_4869197 : Nat := 4983230072969 + 3 ^ 40 * 4869197 * 2
def baseEnd_4869197 : Nat := 833412820810163659348159

theorem tailTrace_4869197 : CollatzResearch.WordTrace tailWord_4869197 prefixEnd_4869197 833412820810163659348159 := by
  unfold tailWord_4869197
  simp only [CollatzResearch.WordTrace]
  refine ⟨177594204540738336486237845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118396136360492224324158563 177594204540738336486237845)
  ·
    refine ⟨8324728337847109522792399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177594204540738336486237845 8324728337847109522792399)
    ·
      refine ⟨12487092506770664284188599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8324728337847109522792399 12487092506770664284188599)
      ·
        refine ⟨18730638760155996426282899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12487092506770664284188599 18730638760155996426282899)
        ·
          refine ⟨28095958140233994639424349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18730638760155996426282899 28095958140233994639424349)
          ·
            refine ⟨10535984302587747989784131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28095958140233994639424349 10535984302587747989784131)
            ·
              refine ⟨15803976453881621984676197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10535984302587747989784131 15803976453881621984676197)
              ·
                refine ⟨2963245585102804122126787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15803976453881621984676197 2963245585102804122126787)
                ·
                  refine ⟨4444868377654206183190181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963245585102804122126787 4444868377654206183190181)
                  ·
                    refine ⟨833412820810163659348159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4444868377654206183190181 833412820810163659348159)
                    ·
                      rfl

theorem cell23_4869197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4869197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869197 prefixEnd_4869197 := by exact prefixLift 4869197
  have htrace : WordTrace (prefixWord ++ tailWord_4869197) baseStart_4869197 baseEnd_4869197 := by
    simpa [prefixWord, tailWord_4869197, baseEnd_4869197] using wordTrace_append hprefix tailTrace_4869197
  have hstable : (prefixWord ++ tailWord_4869197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869197).length < 2 ^ (prefixWord ++ tailWord_4869197).sum := by decide
  have hdescent : baseEnd_4869197 < baseStart_4869197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869199 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7]
def baseStart_4869199 : Nat := 118140960795 + 4869199 * 2 ^ 59
def prefixEnd_4869199 : Nat := 4983230072969 + 3 ^ 40 * 4869199 * 2
def baseEnd_4869199 : Nat := 2500239489391799970219467

theorem tailTrace_4869199 : CollatzResearch.WordTrace tailWord_4869199 prefixEnd_4869199 2500239489391799970219467 := by
  unfold tailWord_4869199
  simp only [CollatzResearch.WordTrace]
  refine ⟨177594277486731090827810651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118396184991154060551873767 177594277486731090827810651)
  ·
    refine ⟨266391416230096636241715977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177594277486731090827810651 266391416230096636241715977)
    ·
      refine ⟨199793562172572477181286983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266391416230096636241715977 199793562172572477181286983)
      ·
        refine ⟨299690343258858715771930475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199793562172572477181286983 299690343258858715771930475)
        ·
          refine ⟨449535514888288073657895713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299690343258858715771930475 449535514888288073657895713)
          ·
            refine ⟨337151636166216055243421785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449535514888288073657895713 337151636166216055243421785)
            ·
              refine ⟨252863727124662041432566339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337151636166216055243421785 252863727124662041432566339)
              ·
                refine ⟨379295590686993062148849509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252863727124662041432566339 379295590686993062148849509)
                ·
                  refine ⟨71117923253811199152909283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 379295590686993062148849509 71117923253811199152909283)
                  ·
                    refine ⟨106676884880716798729363925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71117923253811199152909283 106676884880716798729363925)
                    ·
                      refine ⟨2500239489391799970219467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106676884880716798729363925 2500239489391799970219467)
                      ·
                        rfl

theorem cell23_4869199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_4869199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869199 prefixEnd_4869199 := by exact prefixLift 4869199
  have htrace : WordTrace (prefixWord ++ tailWord_4869199) baseStart_4869199 baseEnd_4869199 := by
    simpa [prefixWord, tailWord_4869199, baseEnd_4869199] using wordTrace_append hprefix tailTrace_4869199
  have hstable : (prefixWord ++ tailWord_4869199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869199).length < 2 ^ (prefixWord ++ tailWord_4869199).sum := by decide
  have hdescent : baseEnd_4869199 < baseStart_4869199 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869224 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_4869224 : Nat := 118140960795 + 4869224 * 2 ^ 59
def prefixEnd_4869224 : Nat := 4983230072969 + 3 ^ 40 * 4869224 * 2
def baseEnd_4869224 : Nat := 2500252326408162372406853

theorem tailTrace_4869224 : CollatzResearch.WordTrace tailWord_4869224 prefixEnd_4869224 2500252326408162372406853 := by
  unfold tailWord_4869224
  simp only [CollatzResearch.WordTrace]
  refine ⟨88797594655820260048735363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118396792874427013398313817 88797594655820260048735363)
  ·
    refine ⟨133196391983730390073103045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88797594655820260048735363 133196391983730390073103045)
    ·
      refine ⟨24974323496949448138706821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133196391983730390073103045 24974323496949448138706821)
      ·
        refine ⟨4682685655678021526007529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24974323496949448138706821 4682685655678021526007529)
        ·
          refine ⟨3512014241758516144505647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4682685655678021526007529 3512014241758516144505647)
          ·
            refine ⟨5268021362637774216758471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512014241758516144505647 5268021362637774216758471)
            ·
              refine ⟨7902032043956661325137707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268021362637774216758471 7902032043956661325137707)
              ·
                refine ⟨11853048065934991987706561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7902032043956661325137707 11853048065934991987706561)
                ·
                  refine ⟨8889786049451243990779921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11853048065934991987706561 8889786049451243990779921)
                  ·
                    refine ⟨6667339537088432993084941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8889786049451243990779921 6667339537088432993084941)
                    ·
                      refine ⟨2500252326408162372406853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6667339537088432993084941 2500252326408162372406853)
                      ·
                        rfl

theorem cell23_4869224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_4869224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869224 prefixEnd_4869224 := by exact prefixLift 4869224
  have htrace : WordTrace (prefixWord ++ tailWord_4869224) baseStart_4869224 baseEnd_4869224 := by
    simpa [prefixWord, tailWord_4869224, baseEnd_4869224] using wordTrace_append hprefix tailTrace_4869224
  have hstable : (prefixWord ++ tailWord_4869224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869224).length < 2 ^ (prefixWord ++ tailWord_4869224).sum := by decide
  have hdescent : baseEnd_4869224 < baseStart_4869224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869230 : List Nat := [4, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2]
def baseStart_4869230 : Nat := 118140960795 + 4869230 * 2 ^ 59
def prefixEnd_4869230 : Nat := 4983230072969 + 3 ^ 40 * 4869230 * 2
def baseEnd_4869230 : Nat := 2500255407292089348931825

theorem tailTrace_4869230 : CollatzResearch.WordTrace tailWord_4869230 prefixEnd_4869230 2500255407292089348931825 := by
  unfold tailWord_4869230
  simp only [CollatzResearch.WordTrace]
  refine ⟨22199426018702347890273643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118396938766412522081459429 22199426018702347890273643)
  ·
    refine ⟨33299139028053521835410465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22199426018702347890273643 33299139028053521835410465)
    ·
      refine ⟨24974354271040141376557849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33299139028053521835410465 24974354271040141376557849)
      ·
        refine ⟨18730765703280106032418387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24974354271040141376557849 18730765703280106032418387)
        ·
          refine ⟨28096148554920159048627581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18730765703280106032418387 28096148554920159048627581)
          ·
            refine ⟨10536055708095059643235343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28096148554920159048627581 10536055708095059643235343)
            ·
              refine ⟨15804083562142589464853015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10536055708095059643235343 15804083562142589464853015)
              ·
                refine ⟨23706125343213884197279523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15804083562142589464853015 23706125343213884197279523)
                ·
                  refine ⟨35559188014820826295919285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23706125343213884197279523 35559188014820826295919285)
                  ·
                    refine ⟨3333673876389452465242433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35559188014820826295919285 3333673876389452465242433)
                    ·
                      refine ⟨2500255407292089348931825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333673876389452465242433 2500255407292089348931825)
                      ·
                        rfl

theorem cell23_4869230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_4869230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869230 prefixEnd_4869230 := by exact prefixLift 4869230
  have htrace : WordTrace (prefixWord ++ tailWord_4869230) baseStart_4869230 baseEnd_4869230 := by
    simpa [prefixWord, tailWord_4869230, baseEnd_4869230] using wordTrace_append hprefix tailTrace_4869230
  have hstable : (prefixWord ++ tailWord_4869230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869230).length < 2 ^ (prefixWord ++ tailWord_4869230).sum := by decide
  have hdescent : baseEnd_4869230 < baseStart_4869230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869280 : List Nat := [2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3]
def baseStart_4869280 : Nat := 118140960795 + 4869280 * 2 ^ 59
def prefixEnd_4869280 : Nat := 4983230072969 + 3 ^ 40 * 4869280 * 2
def baseEnd_4869280 : Nat := 2500281081324814153306595

theorem tailTrace_4869280 : CollatzResearch.WordTrace tailWord_4869280 prefixEnd_4869280 2500281081324814153306595 := by
  unfold tailWord_4869280
  simp only [CollatzResearch.WordTrace]
  refine ⟨88798615899718820830754647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118398154532958427774339529 88798615899718820830754647)
  ·
    refine ⟨133197923849578231246131971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88798615899718820830754647 133197923849578231246131971)
    ·
      refine ⟨199796885774367346869197957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133197923849578231246131971 199796885774367346869197957)
      ·
        refine ⟨37461916082693877537974617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199796885774367346869197957 37461916082693877537974617)
        ·
          refine ⟨28096437062020408153480963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37461916082693877537974617 28096437062020408153480963)
          ·
            refine ⟨42144655593030612230221445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28096437062020408153480963 42144655593030612230221445)
            ·
              refine ⟨7902122923693239793166521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42144655593030612230221445 7902122923693239793166521)
              ·
                refine ⟨5926592192769929844874891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7902122923693239793166521 5926592192769929844874891)
                ·
                  refine ⟨8889888289154894767312337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5926592192769929844874891 8889888289154894767312337)
                  ·
                    refine ⟨6667416216866171075484253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8889888289154894767312337 6667416216866171075484253)
                    ·
                      refine ⟨2500281081324814153306595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6667416216866171075484253 2500281081324814153306595)
                      ·
                        rfl

theorem cell23_4869280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_4869280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869280 prefixEnd_4869280 := by exact prefixLift 4869280
  have htrace : WordTrace (prefixWord ++ tailWord_4869280) baseStart_4869280 baseEnd_4869280 := by
    simpa [prefixWord, tailWord_4869280, baseEnd_4869280] using wordTrace_append hprefix tailTrace_4869280
  have hstable : (prefixWord ++ tailWord_4869280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869280).length < 2 ^ (prefixWord ++ tailWord_4869280).sum := by decide
  have hdescent : baseEnd_4869280 < baseStart_4869280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869306 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_4869306 : Nat := 118140960795 + 4869306 * 2 ^ 59
def prefixEnd_4869306 : Nat := 4983230072969 + 3 ^ 40 * 4869306 * 2
def baseEnd_4869306 : Nat := 2500294431821831051581475

theorem tailTrace_4869306 : CollatzResearch.WordTrace tailWord_4869306 prefixEnd_4869306 2500294431821831051581475 := by
  unfold tailWord_4869306
  simp only [CollatzResearch.WordTrace]
  refine ⟨44399545024335862025488943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118398786731562298734637181 44399545024335862025488943)
  ·
    refine ⟨66599317536503793038233415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44399545024335862025488943 66599317536503793038233415)
    ·
      refine ⟨99898976304755689557350123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66599317536503793038233415 99898976304755689557350123)
      ·
        refine ⟨149848464457133534336025185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99898976304755689557350123 149848464457133534336025185)
        ·
          refine ⟨112386348342850150752018889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149848464457133534336025185 112386348342850150752018889)
          ·
            refine ⟨84289761257137613064014167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112386348342850150752018889 84289761257137613064014167)
            ·
              refine ⟨126434641885706419596021251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84289761257137613064014167 126434641885706419596021251)
              ·
                refine ⟨189651962828559629394031877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126434641885706419596021251 189651962828559629394031877)
                ·
                  refine ⟨35559743030354930511380977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189651962828559629394031877 35559743030354930511380977)
                  ·
                    refine ⟨26669807272766197883535733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35559743030354930511380977 26669807272766197883535733)
                    ·
                      refine ⟨2500294431821831051581475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26669807272766197883535733 2500294431821831051581475)
                      ·
                        rfl

theorem cell23_4869306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_4869306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869306 prefixEnd_4869306 := by exact prefixLift 4869306
  have htrace : WordTrace (prefixWord ++ tailWord_4869306) baseStart_4869306 baseEnd_4869306 := by
    simpa [prefixWord, tailWord_4869306, baseEnd_4869306] using wordTrace_append hprefix tailTrace_4869306
  have hstable : (prefixWord ++ tailWord_4869306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869306).length < 2 ^ (prefixWord ++ tailWord_4869306).sum := by decide
  have hdescent : baseEnd_4869306 < baseStart_4869306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869354 : List Nat := [3, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_4869354 : Nat := 118140960795 + 4869354 * 2 ^ 59
def prefixEnd_4869354 : Nat := 4983230072969 + 3 ^ 40 * 4869354 * 2
def baseEnd_4869354 : Nat := 2500319078893246863781255

theorem tailTrace_4869354 : CollatzResearch.WordTrace tailWord_4869354 prefixEnd_4869354 2500319078893246863781255 := by
  unfold tailWord_4869354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44399982700292388074925779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118399953867446368199802077 44399982700292388074925779)
  ·
    refine ⟨66599974050438582112388669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44399982700292388074925779 66599974050438582112388669)
    ·
      refine ⟨24974990268914468292145751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66599974050438582112388669 24974990268914468292145751)
      ·
        refine ⟨37462485403371702438218627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24974990268914468292145751 37462485403371702438218627)
        ·
          refine ⟨56193728105057553657327941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37462485403371702438218627 56193728105057553657327941)
          ·
            refine ⟨10536324019698291310748989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56193728105057553657327941 10536324019698291310748989)
            ·
              refine ⟨3951121507386859241530871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10536324019698291310748989 3951121507386859241530871)
              ·
                refine ⟨5926682261080288862296307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951121507386859241530871 5926682261080288862296307)
                ·
                  refine ⟨8890023391620433293444461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5926682261080288862296307 8890023391620433293444461)
                  ·
                    refine ⟨3333758771857662485041673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8890023391620433293444461 3333758771857662485041673)
                    ·
                      refine ⟨2500319078893246863781255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333758771857662485041673 2500319078893246863781255)
                      ·
                        rfl

theorem cell23_4869354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_4869354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869354 prefixEnd_4869354 := by exact prefixLift 4869354
  have htrace : WordTrace (prefixWord ++ tailWord_4869354) baseStart_4869354 baseEnd_4869354 := by
    simpa [prefixWord, tailWord_4869354, baseEnd_4869354] using wordTrace_append hprefix tailTrace_4869354
  have hstable : (prefixWord ++ tailWord_4869354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869354).length < 2 ^ (prefixWord ++ tailWord_4869354).sum := by decide
  have hdescent : baseEnd_4869354 < baseStart_4869354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869376 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8]
def baseStart_4869376 : Nat := 118140960795 + 4869376 * 2 ^ 59
def prefixEnd_4869376 : Nat := 4983230072969 + 3 ^ 40 * 4869376 * 2
def baseEnd_4869376 : Nat := 2500330375467645777706153

theorem tailTrace_4869376 : CollatzResearch.WordTrace tailWord_4869376 prefixEnd_4869376 2500330375467645777706153 := by
  unfold tailWord_4869376
  simp only [CollatzResearch.WordTrace]
  refine ⟨88800366603544925028501991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118400488804726566704669321 88800366603544925028501991)
  ·
    refine ⟨133200549905317387542752987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88800366603544925028501991 133200549905317387542752987)
    ·
      refine ⟨199800824857976081314129481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133200549905317387542752987 199800824857976081314129481)
      ·
        refine ⟨149850618643482060985597111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199800824857976081314129481 149850618643482060985597111)
        ·
          refine ⟨224775927965223091478395667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149850618643482060985597111 224775927965223091478395667)
          ·
            refine ⟨337163891947834637217593501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224775927965223091478395667 337163891947834637217593501)
            ·
              refine ⟨126436459480437988956597563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337163891947834637217593501 126436459480437988956597563)
              ·
                refine ⟨189654689220656983434896345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126436459480437988956597563 189654689220656983434896345)
                ·
                  refine ⟨142241016915492737576172259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189654689220656983434896345 142241016915492737576172259)
                  ·
                    refine ⟨213361525373239106364258389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142241016915492737576172259 213361525373239106364258389)
                    ·
                      refine ⟨2500330375467645777706153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213361525373239106364258389 2500330375467645777706153)
                      ·
                        rfl

theorem cell23_4869376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_4869376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869376 prefixEnd_4869376 := by exact prefixLift 4869376
  have htrace : WordTrace (prefixWord ++ tailWord_4869376) baseStart_4869376 baseEnd_4869376 := by
    simpa [prefixWord, tailWord_4869376, baseEnd_4869376] using wordTrace_append hprefix tailTrace_4869376
  have hstable : (prefixWord ++ tailWord_4869376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869376).length < 2 ^ (prefixWord ++ tailWord_4869376).sum := by decide
  have hdescent : baseEnd_4869376 < baseStart_4869376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869380 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_4869380 : Nat := 118140960795 + 4869380 * 2 ^ 59
def prefixEnd_4869380 : Nat := 4983230072969 + 3 ^ 40 * 4869380 * 2
def baseEnd_4869380 : Nat := 2500332429390263762056135

theorem tailTrace_4869380 : CollatzResearch.WordTrace tailWord_4869380 prefixEnd_4869380 2500332429390263762056135 := by
  unfold tailWord_4869380
  simp only [CollatzResearch.WordTrace]
  refine ⟨88800439549537679370074797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118400586066050239160099729 88800439549537679370074797)
  ·
    refine ⟨33300164831076629763778049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88800439549537679370074797 33300164831076629763778049)
    ·
      refine ⟨24975123623307472322833537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33300164831076629763778049 24975123623307472322833537)
      ·
        refine ⟨18731342717480604242125153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24975123623307472322833537 18731342717480604242125153)
        ·
          refine ⟨14048507038110453181593865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18731342717480604242125153 14048507038110453181593865)
          ·
            refine ⟨10536380278582839886195399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14048507038110453181593865 10536380278582839886195399)
            ·
              refine ⟨15804570417874259829293099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10536380278582839886195399 15804570417874259829293099)
              ·
                refine ⟨23706855626811389743939649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15804570417874259829293099 23706855626811389743939649)
                ·
                  refine ⟨17780141720108542307954737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23706855626811389743939649 17780141720108542307954737)
                  ·
                    refine ⟨13335106290081406730966053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17780141720108542307954737 13335106290081406730966053)
                    ·
                      refine ⟨2500332429390263762056135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13335106290081406730966053 2500332429390263762056135)
                      ·
                        rfl

theorem cell23_4869380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_4869380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869380 prefixEnd_4869380 := by exact prefixLift 4869380
  have htrace : WordTrace (prefixWord ++ tailWord_4869380) baseStart_4869380 baseEnd_4869380 := by
    simpa [prefixWord, tailWord_4869380, baseEnd_4869380] using wordTrace_append hprefix tailTrace_4869380
  have hstable : (prefixWord ++ tailWord_4869380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869380).length < 2 ^ (prefixWord ++ tailWord_4869380).sum := by decide
  have hdescent : baseEnd_4869380 < baseStart_4869380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869407 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 5]
def baseStart_4869407 : Nat := 118140960795 + 4869407 * 2 ^ 59
def prefixEnd_4869407 : Nat := 4983230072969 + 3 ^ 40 * 4869407 * 2
def baseEnd_4869407 : Nat := 277816254818659461824279

theorem tailTrace_4869407 : CollatzResearch.WordTrace tailWord_4869407 prefixEnd_4869407 277816254818659461824279 := by
  unfold tailWord_4869407
  simp only [CollatzResearch.WordTrace]
  refine ⟨177601863869977542351382475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118401242579985028234254983 177601863869977542351382475)
  ·
    refine ⟨266402795804966313527073713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177601863869977542351382475 266402795804966313527073713)
    ·
      refine ⟨199802096853724735145305285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266402795804966313527073713 199802096853724735145305285)
      ·
        refine ⟨37462893160073387839744741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199802096853724735145305285 37462893160073387839744741)
        ·
          refine ⟨7024292467513760219952139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37462893160073387839744741 7024292467513760219952139)
          ·
            refine ⟨10536438701270640329928209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7024292467513760219952139 10536438701270640329928209)
            ·
              refine ⟨7902329025952980247446157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10536438701270640329928209 7902329025952980247446157)
              ·
                refine ⟨2963373384732367592792309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7902329025952980247446157 2963373384732367592792309)
                ·
                  refine ⟨277816254818659461824279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2963373384732367592792309 277816254818659461824279)
                  ·
                    rfl

theorem cell23_4869407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 5].length) (baseStart_4869407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869407 prefixEnd_4869407 := by exact prefixLift 4869407
  have htrace : WordTrace (prefixWord ++ tailWord_4869407) baseStart_4869407 baseEnd_4869407 := by
    simpa [prefixWord, tailWord_4869407, baseEnd_4869407] using wordTrace_append hprefix tailTrace_4869407
  have hstable : (prefixWord ++ tailWord_4869407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869407).length < 2 ^ (prefixWord ++ tailWord_4869407).sum := by decide
  have hdescent : baseEnd_4869407 < baseStart_4869407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869423 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_4869423 : Nat := 118140960795 + 4869423 * 2 ^ 59
def prefixEnd_4869423 : Nat := 4983230072969 + 3 ^ 40 * 4869423 * 2
def baseEnd_4869423 : Nat := 2500354509058407093818437

theorem tailTrace_4869423 : CollatzResearch.WordTrace tailWord_4869423 prefixEnd_4869423 2500354509058407093818437 := by
  unfold tailWord_4869423
  simp only [CollatzResearch.WordTrace]
  refine ⟨177602447437919577083964923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118401631625279718055976615 177602447437919577083964923)
  ·
    refine ⟨266403671156879365625947385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177602447437919577083964923 266403671156879365625947385)
    ·
      refine ⟨199802753367659524219460539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266403671156879365625947385 199802753367659524219460539)
      ·
        refine ⟨299704130051489286329190809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199802753367659524219460539 299704130051489286329190809)
        ·
          refine ⟨224778097538616964746893107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299704130051489286329190809 224778097538616964746893107)
          ·
            refine ⟨337167146307925447120339661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224778097538616964746893107 337167146307925447120339661)
            ·
              refine ⟨126437679865472042670127373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337167146307925447120339661 126437679865472042670127373)
              ·
                refine ⟨47414129949552016001297765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126437679865472042670127373 47414129949552016001297765)
                ·
                  refine ⟨8890149365541003000243331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47414129949552016001297765 8890149365541003000243331)
                  ·
                    refine ⟨13335224048311504500364997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8890149365541003000243331 13335224048311504500364997)
                    ·
                      refine ⟨2500354509058407093818437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13335224048311504500364997 2500354509058407093818437)
                      ·
                        rfl

theorem cell23_4869423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_4869423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869423 prefixEnd_4869423 := by exact prefixLift 4869423
  have htrace : WordTrace (prefixWord ++ tailWord_4869423) baseStart_4869423 baseEnd_4869423 := by
    simpa [prefixWord, tailWord_4869423, baseEnd_4869423] using wordTrace_append hprefix tailTrace_4869423
  have hstable : (prefixWord ++ tailWord_4869423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869423).length < 2 ^ (prefixWord ++ tailWord_4869423).sum := by decide
  have hdescent : baseEnd_4869423 < baseStart_4869423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869440 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2]
def baseStart_4869440 : Nat := 118140960795 + 4869440 * 2 ^ 59
def prefixEnd_4869440 : Nat := 4983230072969 + 3 ^ 40 * 4869440 * 2
def baseEnd_4869440 : Nat := 2500363238229533527305859

theorem tailTrace_4869440 : CollatzResearch.WordTrace tailWord_4869440 prefixEnd_4869440 2500363238229533527305859 := by
  unfold tailWord_4869440
  simp only [CollatzResearch.WordTrace]
  refine ⟨88801533739428994493666887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118402044985905325991555849 88801533739428994493666887)
  ·
    refine ⟨133202300609143491740500331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88801533739428994493666887 133202300609143491740500331)
    ·
      refine ⟨199803450913715237610750497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133202300609143491740500331 199803450913715237610750497)
      ·
        refine ⟨149852588185286428208062873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199803450913715237610750497 149852588185286428208062873)
        ·
          refine ⟨112389441138964821156047155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149852588185286428208062873 112389441138964821156047155)
          ·
            refine ⟨168584161708447231734070733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112389441138964821156047155 168584161708447231734070733)
            ·
              refine ⟨63219060640667711900276525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168584161708447231734070733 63219060640667711900276525)
              ·
                refine ⟨23707147740250391962603697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63219060640667711900276525 23707147740250391962603697)
                ·
                  refine ⟨17780360805187793971952773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23707147740250391962603697 17780360805187793971952773)
                  ·
                    refine ⟨3333817650972711369741145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17780360805187793971952773 3333817650972711369741145)
                    ·
                      refine ⟨2500363238229533527305859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333817650972711369741145 2500363238229533527305859)
                      ·
                        rfl

theorem cell23_4869440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 2, 4, 2].length) (baseStart_4869440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869440 prefixEnd_4869440 := by exact prefixLift 4869440
  have htrace : WordTrace (prefixWord ++ tailWord_4869440) baseStart_4869440 baseEnd_4869440 := by
    simpa [prefixWord, tailWord_4869440, baseEnd_4869440] using wordTrace_append hprefix tailTrace_4869440
  have hstable : (prefixWord ++ tailWord_4869440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869440).length < 2 ^ (prefixWord ++ tailWord_4869440).sum := by decide
  have hdescent : baseEnd_4869440 < baseStart_4869440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869460 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_4869460 : Nat := 118140960795 + 4869460 * 2 ^ 59
def prefixEnd_4869460 : Nat := 4983230072969 + 3 ^ 40 * 4869460 * 2
def baseEnd_4869460 : Nat := 2500373507842623449055767

theorem tailTrace_4869460 : CollatzResearch.WordTrace tailWord_4869460 prefixEnd_4869460 2500373507842623449055767 := by
  unfold tailWord_4869460
  simp only [CollatzResearch.WordTrace]
  refine ⟨88801898469392766201530917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118402531292523688268707889 88801898469392766201530917)
  ·
    refine ⟨16650355963011143662787047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88801898469392766201530917 16650355963011143662787047)
    ·
      refine ⟨24975533944516715494180571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16650355963011143662787047 24975533944516715494180571)
      ·
        refine ⟨37463300916775073241270857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24975533944516715494180571 37463300916775073241270857)
        ·
          refine ⟨28097475687581304930953143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37463300916775073241270857 28097475687581304930953143)
          ·
            refine ⟨42146213531371957396429715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28097475687581304930953143 42146213531371957396429715)
            ·
              refine ⟨63219320297057936094644573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42146213531371957396429715 63219320297057936094644573)
              ·
                refine ⟨23707245111396726035491715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63219320297057936094644573 23707245111396726035491715)
                ·
                  refine ⟨35560867667095089053237573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23707245111396726035491715 35560867667095089053237573)
                  ·
                    refine ⟨6667662687580329197482045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35560867667095089053237573 6667662687580329197482045)
                    ·
                      refine ⟨2500373507842623449055767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6667662687580329197482045 2500373507842623449055767)
                      ·
                        rfl

theorem cell23_4869460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_4869460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869460 prefixEnd_4869460 := by exact prefixLift 4869460
  have htrace : WordTrace (prefixWord ++ tailWord_4869460) baseStart_4869460 baseEnd_4869460 := by
    simpa [prefixWord, tailWord_4869460, baseEnd_4869460] using wordTrace_append hprefix tailTrace_4869460
  have hstable : (prefixWord ++ tailWord_4869460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869460).length < 2 ^ (prefixWord ++ tailWord_4869460).sum := by decide
  have hdescent : baseEnd_4869460 < baseStart_4869460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869463 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 8]
def baseStart_4869463 : Nat := 118140960795 + 4869463 * 2 ^ 59
def prefixEnd_4869463 : Nat := 4983230072969 + 3 ^ 40 * 4869463 * 2
def baseEnd_4869463 : Nat := 277819449809398548590917

theorem tailTrace_4869463 : CollatzResearch.WordTrace tailWord_4869463 prefixEnd_4869463 277819449809398548590917 := by
  unfold tailWord_4869463
  simp only [CollatzResearch.WordTrace]
  refine ⟨177603906357774663915421043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118402604238516442610280695 177603906357774663915421043)
  ·
    refine ⟨266405859536661995873131565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177603906357774663915421043 266405859536661995873131565)
    ·
      refine ⟨99902197326248248452424337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266405859536661995873131565 99902197326248248452424337)
      ·
        refine ⟨74926647994686186339318253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99902197326248248452424337 74926647994686186339318253)
        ·
          refine ⟨28097492998007319877244345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74926647994686186339318253 28097492998007319877244345)
          ·
            refine ⟨21073119748505489907933259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28097492998007319877244345 21073119748505489907933259)
            ·
              refine ⟨31609679622758234861899889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21073119748505489907933259 31609679622758234861899889)
              ·
                refine ⟨23707259717068676146424917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31609679622758234861899889 23707259717068676146424917)
                ·
                  refine ⟨277819449809398548590917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23707259717068676146424917 277819449809398548590917)
                  ·
                    rfl

theorem cell23_4869463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 8].length) (baseStart_4869463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869463 prefixEnd_4869463 := by exact prefixLift 4869463
  have htrace : WordTrace (prefixWord ++ tailWord_4869463) baseStart_4869463 baseEnd_4869463 := by
    simpa [prefixWord, tailWord_4869463, baseEnd_4869463] using wordTrace_append hprefix tailTrace_4869463
  have hstable : (prefixWord ++ tailWord_4869463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869463).length < 2 ^ (prefixWord ++ tailWord_4869463).sum := by decide
  have hdescent : baseEnd_4869463 < baseStart_4869463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869557 : List Nat := [1, 3, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_4869557 : Nat := 118140960795 + 4869557 * 2 ^ 59
def prefixEnd_4869557 : Nat := 4983230072969 + 3 ^ 40 * 4869557 * 2
def baseEnd_4869557 : Nat := 833474438488703189847607

theorem tailTrace_4869557 : CollatzResearch.WordTrace tailWord_4869557 prefixEnd_4869557 833474438488703189847607 := by
  unfold tailWord_4869557
  simp only [CollatzResearch.WordTrace]
  refine ⟨177607334819434117969342925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118404889879622745312895283 177607334819434117969342925)
  ·
    refine ⟨66602750557287794238503597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177607334819434117969342925 66602750557287794238503597)
    ·
      refine ⟨24976031458982922839438849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66602750557287794238503597 24976031458982922839438849)
      ·
        refine ⟨18732023594237192129579137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24976031458982922839438849 18732023594237192129579137)
        ·
          refine ⟨14049017695677894097184353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18732023594237192129579137 14049017695677894097184353)
          ·
            refine ⟨10536763271758420572888265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14049017695677894097184353 10536763271758420572888265)
            ·
              refine ⟨7902572453818815429666199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10536763271758420572888265 7902572453818815429666199)
              ·
                refine ⟨11853858680728223144499299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7902572453818815429666199 11853858680728223144499299)
                ·
                  refine ⟨17780788021092334716748949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11853858680728223144499299 17780788021092334716748949)
                  ·
                    refine ⟨833474438488703189847607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17780788021092334716748949 833474438488703189847607)
                    ·
                      rfl

theorem cell23_4869557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_4869557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869557 prefixEnd_4869557 := by exact prefixLift 4869557
  have htrace : WordTrace (prefixWord ++ tailWord_4869557) baseStart_4869557 baseEnd_4869557 := by
    simpa [prefixWord, tailWord_4869557, baseEnd_4869557] using wordTrace_append hprefix tailTrace_4869557
  have hstable : (prefixWord ++ tailWord_4869557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869557).length < 2 ^ (prefixWord ++ tailWord_4869557).sum := by decide
  have hdescent : baseEnd_4869557 < baseStart_4869557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869560 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4]
def baseStart_4869560 : Nat := 118140960795 + 4869560 * 2 ^ 59
def prefixEnd_4869560 : Nat := 4983230072969 + 3 ^ 40 * 4869560 * 2
def baseEnd_4869560 : Nat := 2500424855908073057805307

theorem tailTrace_4869560 : CollatzResearch.WordTrace tailWord_4869560 prefixEnd_4869560 2500424855908073057805307 := by
  unfold tailWord_4869560
  simp only [CollatzResearch.WordTrace]
  refine ⟨88803722119211624740851067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118404962825615499654468089 88803722119211624740851067)
  ·
    refine ⟨133205583178817437111276601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88803722119211624740851067 133205583178817437111276601)
    ·
      refine ⟨99904187384113077833457451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133205583178817437111276601 99904187384113077833457451)
      ·
        refine ⟨149856281076169616750186177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99904187384113077833457451 149856281076169616750186177)
        ·
          refine ⟨112392210807127212562639633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149856281076169616750186177 112392210807127212562639633)
          ·
            refine ⟨84294158105345409421979725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112392210807127212562639633 84294158105345409421979725)
            ·
              refine ⟨31610309289504528533242397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84294158105345409421979725 31610309289504528533242397)
              ·
                refine ⟨11853865983564198199965899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31610309289504528533242397 11853865983564198199965899)
                ·
                  refine ⟨17780798975346297299948849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11853865983564198199965899 17780798975346297299948849)
                  ·
                    refine ⟨13335599231509722974961637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17780798975346297299948849 13335599231509722974961637)
                    ·
                      refine ⟨2500424855908073057805307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13335599231509722974961637 2500424855908073057805307)
                      ·
                        rfl

theorem cell23_4869560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_4869560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869560 prefixEnd_4869560 := by exact prefixLift 4869560
  have htrace : WordTrace (prefixWord ++ tailWord_4869560) baseStart_4869560 baseEnd_4869560 := by
    simpa [prefixWord, tailWord_4869560, baseEnd_4869560] using wordTrace_append hprefix tailTrace_4869560
  have hstable : (prefixWord ++ tailWord_4869560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869560).length < 2 ^ (prefixWord ++ tailWord_4869560).sum := by decide
  have hdescent : baseEnd_4869560 < baseStart_4869560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869624 : List Nat := [2, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2]
def baseStart_4869624 : Nat := 118140960795 + 4869624 * 2 ^ 59
def prefixEnd_4869624 : Nat := 4983230072969 + 3 ^ 40 * 4869624 * 2
def baseEnd_4869624 : Nat := 2500457718669960807405013

theorem tailTrace_4869624 : CollatzResearch.WordTrace tailWord_4869624 prefixEnd_4869624 2500457718669960807405013 := by
  unfold tailWord_4869624
  simp only [CollatzResearch.WordTrace]
  refine ⟨88804889255095694206015963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118406519006794258941354617 88804889255095694206015963)
  ·
    refine ⟨133207333882643541309023945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88804889255095694206015963 133207333882643541309023945)
    ·
      refine ⟨99905500411982655981767959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133207333882643541309023945 99905500411982655981767959)
      ·
        refine ⟨149858250617973983972651939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99905500411982655981767959 149858250617973983972651939)
        ·
          refine ⟨224787375926960975958977909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149858250617973983972651939 224787375926960975958977909)
          ·
            refine ⟨21073816493152591496154179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 224787375926960975958977909 21073816493152591496154179)
            ·
              refine ⟨31610724739728887244231269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21073816493152591496154179 31610724739728887244231269)
              ·
                refine ⟨5927010888699166358293363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31610724739728887244231269 5927010888699166358293363)
                ·
                  refine ⟨8890516333048749537440045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5927010888699166358293363 8890516333048749537440045)
                  ·
                    refine ⟨3333943624893281076540017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8890516333048749537440045 3333943624893281076540017)
                    ·
                      refine ⟨2500457718669960807405013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333943624893281076540017 2500457718669960807405013)
                      ·
                        rfl

theorem cell23_4869624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 1, 3, 2].length) (baseStart_4869624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869624 prefixEnd_4869624 := by exact prefixLift 4869624
  have htrace : WordTrace (prefixWord ++ tailWord_4869624) baseStart_4869624 baseEnd_4869624 := by
    simpa [prefixWord, tailWord_4869624, baseEnd_4869624] using wordTrace_append hprefix tailTrace_4869624
  have hstable : (prefixWord ++ tailWord_4869624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869624).length < 2 ^ (prefixWord ++ tailWord_4869624).sum := by decide
  have hdescent : baseEnd_4869624 < baseStart_4869624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869637 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 3, 4, 2]
def baseStart_4869637 : Nat := 118140960795 + 4869637 * 2 ^ 59
def prefixEnd_4869637 : Nat := 4983230072969 + 3 ^ 40 * 4869637 * 2
def baseEnd_4869637 : Nat := 2500464393918469256542453

theorem tailTrace_4869637 : CollatzResearch.WordTrace tailWord_4869637 prefixEnd_4869637 2500464393918469256542453 := by
  unfold tailWord_4869637
  simp only [CollatzResearch.WordTrace]
  refine ⟨177610252659144291632255165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118406835106096194421503443 177610252659144291632255165)
  ·
    refine ⟨66603844747179109362095687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177610252659144291632255165 66603844747179109362095687)
    ·
      refine ⟨99905767120768664043143531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66603844747179109362095687 99905767120768664043143531)
      ·
        refine ⟨149858650681152996064715297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99905767120768664043143531 149858650681152996064715297)
        ·
          refine ⟨112393988010864747048536473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149858650681152996064715297 112393988010864747048536473)
          ·
            refine ⟨84295491008148560286402355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112393988010864747048536473 84295491008148560286402355)
            ·
              refine ⟨126443236512222840429603533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84295491008148560286402355 126443236512222840429603533)
              ·
                refine ⟨47416213692083565161101325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126443236512222840429603533 47416213692083565161101325)
                ·
                  refine ⟨17781080134531336935412997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47416213692083565161101325 17781080134531336935412997)
                  ·
                    refine ⟨3333952525224625675389937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17781080134531336935412997 3333952525224625675389937)
                    ·
                      refine ⟨2500464393918469256542453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3333952525224625675389937 2500464393918469256542453)
                      ·
                        rfl

theorem cell23_4869637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 3, 4, 2].length) (baseStart_4869637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869637 prefixEnd_4869637 := by exact prefixLift 4869637
  have htrace : WordTrace (prefixWord ++ tailWord_4869637) baseStart_4869637 baseEnd_4869637 := by
    simpa [prefixWord, tailWord_4869637, baseEnd_4869637] using wordTrace_append hprefix tailTrace_4869637
  have hstable : (prefixWord ++ tailWord_4869637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869637).length < 2 ^ (prefixWord ++ tailWord_4869637).sum := by decide
  have hdescent : baseEnd_4869637 < baseStart_4869637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869638 : List Nat := [6, 2, 1, 1, 3, 1, 9]
def baseStart_4869638 : Nat := 118140960795 + 4869638 * 2 ^ 59
def prefixEnd_4869638 : Nat := 4983230072969 + 3 ^ 40 * 4869638 * 2
def baseEnd_4869638 : Nat := 30869937128384243859629

theorem tailTrace_4869638 : CollatzResearch.WordTrace tailWord_4869638 prefixEnd_4869638 30869937128384243859629 := by
  unfold tailWord_4869638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550321535379395900095049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118406859421427112535361045 5550321535379395900095049)
  ·
    refine ⟨4162741151534546925071287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5550321535379395900095049 4162741151534546925071287)
    ·
      refine ⟨6244111727301820387606931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4162741151534546925071287 6244111727301820387606931)
      ·
        refine ⟨9366167590952730581410397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6244111727301820387606931 9366167590952730581410397)
        ·
          refine ⟨3512312846607273968028899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9366167590952730581410397 3512312846607273968028899)
          ·
            refine ⟨5268469269910910952043349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512312846607273968028899 5268469269910910952043349)
            ·
              refine ⟨30869937128384243859629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5268469269910910952043349 30869937128384243859629)
              ·
                rfl

theorem cell23_4869638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 9].length) (baseStart_4869638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869638 prefixEnd_4869638 := by exact prefixLift 4869638
  have htrace : WordTrace (prefixWord ++ tailWord_4869638) baseStart_4869638 baseEnd_4869638 := by
    simpa [prefixWord, tailWord_4869638, baseEnd_4869638] using wordTrace_append hprefix tailTrace_4869638
  have hstable : (prefixWord ++ tailWord_4869638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869638).length < 2 ^ (prefixWord ++ tailWord_4869638).sum := by decide
  have hdescent : baseEnd_4869638 < baseStart_4869638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869640 : List Nat := [2, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_4869640 : Nat := 118140960795 + 4869640 * 2 ^ 59
def prefixEnd_4869640 : Nat := 4983230072969 + 3 ^ 40 * 4869640 * 2
def baseEnd_4869640 : Nat := 2500465934360432744804939

theorem tailTrace_4869640 : CollatzResearch.WordTrace tailWord_4869640 prefixEnd_4869640 2500465934360432744804939 := by
  unfold tailWord_4869640
  simp only [CollatzResearch.WordTrace]
  refine ⟨88805181039066711572307187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118406908052088948763076249 88805181039066711572307187)
  ·
    refine ⟨133207771558600067358460781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88805181039066711572307187 133207771558600067358460781)
    ·
      refine ⟨49952914334475025259422793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133207771558600067358460781 49952914334475025259422793)
      ·
        refine ⟨37464685750856268944567095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49952914334475025259422793 37464685750856268944567095)
        ·
          refine ⟨56197028626284403416850643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37464685750856268944567095 56197028626284403416850643)
          ·
            refine ⟨84295542939426605125275965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56197028626284403416850643 84295542939426605125275965)
            ·
              refine ⟨31610828602284976921978487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84295542939426605125275965 31610828602284976921978487)
              ·
                refine ⟨47416242903427465382967731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31610828602284976921978487 47416242903427465382967731)
                ·
                  refine ⟨71124364355141198074451597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47416242903427465382967731 71124364355141198074451597)
                  ·
                    refine ⟨26671636633177949277919349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71124364355141198074451597 26671636633177949277919349)
                    ·
                      refine ⟨2500465934360432744804939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26671636633177949277919349 2500465934360432744804939)
                      ·
                        rfl

theorem cell23_4869640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_4869640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869640 prefixEnd_4869640 := by exact prefixLift 4869640
  have htrace : WordTrace (prefixWord ++ tailWord_4869640) baseStart_4869640 baseEnd_4869640 := by
    simpa [prefixWord, tailWord_4869640, baseEnd_4869640] using wordTrace_append hprefix tailTrace_4869640
  have hstable : (prefixWord ++ tailWord_4869640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869640).length < 2 ^ (prefixWord ++ tailWord_4869640).sum := by decide
  have hdescent : baseEnd_4869640 < baseStart_4869640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869714 : List Nat := [3, 2, 2, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_4869714 : Nat := 118140960795 + 4869714 * 2 ^ 59
def prefixEnd_4869714 : Nat := 4983230072969 + 3 ^ 40 * 4869714 * 2
def baseEnd_4869714 : Nat := 2500503931928865455279599

theorem tailTrace_4869714 : CollatzResearch.WordTrace tailWord_4869714 prefixEnd_4869714 2500503931928865455279599 := by
  unfold tailWord_4869714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44403265269966333445702049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118408707386576889188538797 44403265269966333445702049)
  ·
    refine ⟨33302448952474750084276537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44403265269966333445702049 33302448952474750084276537)
    ·
      refine ⟨24976836714356062563207403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33302448952474750084276537 24976836714356062563207403)
      ·
        refine ⟨37465255071534093844811105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24976836714356062563207403 37465255071534093844811105)
        ·
          refine ⟨28098941303650570383608329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37465255071534093844811105 28098941303650570383608329)
          ·
            refine ⟨21074205977737927787706247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28098941303650570383608329 21074205977737927787706247)
            ·
              refine ⟨31611308966606891681559371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21074205977737927787706247 31611308966606891681559371)
              ·
                refine ⟨47416963449910337522339057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31611308966606891681559371 47416963449910337522339057)
                ·
                  refine ⟨35562722587432753141754293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47416963449910337522339057 35562722587432753141754293)
                  ·
                    refine ⟨3334005242571820607039465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35562722587432753141754293 3334005242571820607039465)
                    ·
                      refine ⟨2500503931928865455279599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334005242571820607039465 2500503931928865455279599)
                      ·
                        rfl

theorem cell23_4869714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_4869714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869714 prefixEnd_4869714 := by exact prefixLift 4869714
  have htrace : WordTrace (prefixWord ++ tailWord_4869714) baseStart_4869714 baseEnd_4869714 := by
    simpa [prefixWord, tailWord_4869714, baseEnd_4869714] using wordTrace_append hprefix tailTrace_4869714
  have hstable : (prefixWord ++ tailWord_4869714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869714).length < 2 ^ (prefixWord ++ tailWord_4869714).sum := by decide
  have hdescent : baseEnd_4869714 < baseStart_4869714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869718 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4869718 : Nat := 118140960795 + 4869718 * 2 ^ 59
def prefixEnd_4869718 : Nat := 4983230072969 + 3 ^ 40 * 4869718 * 2
def baseEnd_4869718 : Nat := 2500505985851483439629581

theorem tailTrace_4869718 : CollatzResearch.WordTrace tailWord_4869718 prefixEnd_4869718 2500505985851483439629581 := by
  unfold tailWord_4869718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11100825435740677654122113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118408804647900561643969205 11100825435740677654122113)
  ·
    refine ⟨8325619076805508240591585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11100825435740677654122113 8325619076805508240591585)
    ·
      refine ⟨6244214307604131180443689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8325619076805508240591585 6244214307604131180443689)
      ·
        refine ⟨4683160730703098385332767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6244214307604131180443689 4683160730703098385332767)
        ·
          refine ⟨7024741096054647577999151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683160730703098385332767 7024741096054647577999151)
          ·
            refine ⟨10537111644081971366998727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7024741096054647577999151 10537111644081971366998727)
            ·
              refine ⟨15805667466122957050498091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10537111644081971366998727 15805667466122957050498091)
              ·
                refine ⟨23708501199184435575747137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15805667466122957050498091 23708501199184435575747137)
                ·
                  refine ⟨17781375899388326681810353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23708501199184435575747137 17781375899388326681810353)
                  ·
                    refine ⟨13336031924541245011357765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17781375899388326681810353 13336031924541245011357765)
                    ·
                      refine ⟨2500505985851483439629581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13336031924541245011357765 2500505985851483439629581)
                      ·
                        rfl

theorem cell23_4869718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4869718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869718 prefixEnd_4869718 := by exact prefixLift 4869718
  have htrace : WordTrace (prefixWord ++ tailWord_4869718) baseStart_4869718 baseEnd_4869718 := by
    simpa [prefixWord, tailWord_4869718, baseEnd_4869718] using wordTrace_append hprefix tailTrace_4869718
  have hstable : (prefixWord ++ tailWord_4869718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869718).length < 2 ^ (prefixWord ++ tailWord_4869718).sum := by decide
  have hdescent : baseEnd_4869718 < baseStart_4869718 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869720 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 2, 8]
def baseStart_4869720 : Nat := 118140960795 + 4869720 * 2 ^ 59
def prefixEnd_4869720 : Nat := 4983230072969 + 3 ^ 40 * 4869720 * 2
def baseEnd_4869720 : Nat := 833502337604264143934857

theorem tailTrace_4869720 : CollatzResearch.WordTrace tailWord_4869720 prefixEnd_4869720 833502337604264143934857 := by
  unfold tailWord_4869720
  simp only [CollatzResearch.WordTrace]
  refine ⟨88806639958921798403763307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118408853278562397871684409 88806639958921798403763307)
  ·
    refine ⟨133209959938382697605644961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88806639958921798403763307 133209959938382697605644961)
    ·
      refine ⟨99907469953787023204233721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133209959938382697605644961 99907469953787023204233721)
      ·
        refine ⟨74930602465340267403175291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99907469953787023204233721 74930602465340267403175291)
        ·
          refine ⟨112395903698010401104762937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74930602465340267403175291 112395903698010401104762937)
          ·
            refine ⟨84296927773507800828572203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112395903698010401104762937 84296927773507800828572203)
            ·
              refine ⟨126445391660261701242858305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84296927773507800828572203 126445391660261701242858305)
              ·
                refine ⟨94834043745196275932143729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126445391660261701242858305 94834043745196275932143729)
                ·
                  refine ⟨71125532808897206949107797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94834043745196275932143729 71125532808897206949107797)
                  ·
                    refine ⟨833502337604264143934857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71125532808897206949107797 833502337604264143934857)
                    ·
                      rfl

theorem cell23_4869720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 8].length) (baseStart_4869720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869720 prefixEnd_4869720 := by exact prefixLift 4869720
  have htrace : WordTrace (prefixWord ++ tailWord_4869720) baseStart_4869720 baseEnd_4869720 := by
    simpa [prefixWord, tailWord_4869720, baseEnd_4869720] using wordTrace_append hprefix tailTrace_4869720
  have hstable : (prefixWord ++ tailWord_4869720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869720).length < 2 ^ (prefixWord ++ tailWord_4869720).sum := by decide
  have hdescent : baseEnd_4869720 < baseStart_4869720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869737 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 5, 4]
def baseStart_4869737 : Nat := 118140960795 + 4869737 * 2 ^ 59
def prefixEnd_4869737 : Nat := 4983230072969 + 3 ^ 40 * 4869737 * 2
def baseEnd_4869737 : Nat := 833505247327972955097331

theorem tailTrace_4869737 : CollatzResearch.WordTrace tailWord_4869737 prefixEnd_4869737 833505247327972955097331 := by
  unfold tailWord_4869737
  simp only [CollatzResearch.WordTrace]
  refine ⟨177613899958782008710895465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118409266639188005807263643 177613899958782008710895465)
  ·
    refine ⟨133210424969086506533171599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177613899958782008710895465 133210424969086506533171599)
    ·
      refine ⟨199815637453629759799757399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133210424969086506533171599 199815637453629759799757399)
      ·
        refine ⟨299723456180444639699636099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199815637453629759799757399 299723456180444639699636099)
        ·
          refine ⟨449585184270666959549454149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299723456180444639699636099 449585184270666959549454149)
          ·
            refine ⟨84297222050750054915522653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 449585184270666959549454149 84297222050750054915522653)
            ·
              refine ⟨31611458269031270593320995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84297222050750054915522653 31611458269031270593320995)
              ·
                refine ⟨47417187403546905889981493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31611458269031270593320995 47417187403546905889981493)
                ·
                  refine ⟨4445361319082522427185765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47417187403546905889981493 4445361319082522427185765)
                  ·
                    refine ⟨833505247327972955097331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445361319082522427185765 833505247327972955097331)
                    ·
                      rfl

theorem cell23_4869737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 5, 4].length) (baseStart_4869737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869737 prefixEnd_4869737 := by exact prefixLift 4869737
  have htrace : WordTrace (prefixWord ++ tailWord_4869737) baseStart_4869737 baseEnd_4869737 := by
    simpa [prefixWord, tailWord_4869737, baseEnd_4869737] using wordTrace_append hprefix tailTrace_4869737
  have hstable : (prefixWord ++ tailWord_4869737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869737).length < 2 ^ (prefixWord ++ tailWord_4869737).sum := by decide
  have hdescent : baseEnd_4869737 < baseStart_4869737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869741 : List Nat := [1, 5, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_4869741 : Nat := 118140960795 + 4869741 * 2 ^ 59
def prefixEnd_4869741 : Nat := 4983230072969 + 3 ^ 40 * 4869741 * 2
def baseEnd_4869741 : Nat := 833505931968845616547325

theorem tailTrace_4869741 : CollatzResearch.WordTrace tailWord_4869741 prefixEnd_4869741 833505931968845616547325 := by
  unfold tailWord_4869741
  simp only [CollatzResearch.WordTrace]
  refine ⟨177614045850767517394041077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118409363900511678262694051 177614045850767517394041077)
  ·
    refine ⟨16651316798509454755691351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177614045850767517394041077 16651316798509454755691351)
    ·
      refine ⟨24976975197764182133537027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16651316798509454755691351 24976975197764182133537027)
      ·
        refine ⟨37465462796646273200305541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24976975197764182133537027 37465462796646273200305541)
        ·
          refine ⟨7024774274371176225057289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37465462796646273200305541 7024774274371176225057289)
          ·
            refine ⟨5268580705778382168792967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7024774274371176225057289 5268580705778382168792967)
            ·
              refine ⟨7902871058667573253189451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268580705778382168792967 7902871058667573253189451)
              ·
                refine ⟨11854306588001359879784177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7902871058667573253189451 11854306588001359879784177)
                ·
                  refine ⟨8890729941001019909838133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11854306588001359879784177 8890729941001019909838133)
                  ·
                    refine ⟨833505931968845616547325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8890729941001019909838133 833505931968845616547325)
                    ·
                      rfl

theorem cell23_4869741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_4869741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869741 prefixEnd_4869741 := by exact prefixLift 4869741
  have htrace : WordTrace (prefixWord ++ tailWord_4869741) baseStart_4869741 baseEnd_4869741 := by
    simpa [prefixWord, tailWord_4869741, baseEnd_4869741] using wordTrace_append hprefix tailTrace_4869741
  have hstable : (prefixWord ++ tailWord_4869741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869741).length < 2 ^ (prefixWord ++ tailWord_4869741).sum := by decide
  have hdescent : baseEnd_4869741 < baseStart_4869741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869744 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4]
def baseStart_4869744 : Nat := 118140960795 + 4869744 * 2 ^ 59
def prefixEnd_4869744 : Nat := 4983230072969 + 3 ^ 40 * 4869744 * 2
def baseEnd_4869744 : Nat := 2500519336348500337904461

theorem tailTrace_4869744 : CollatzResearch.WordTrace tailWord_4869744 prefixEnd_4869744 2500519336348500337904461 := by
  unfold tailWord_4869744
  simp only [CollatzResearch.WordTrace]
  refine ⟨88807077634878324453200143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118409436846504432604266857 88807077634878324453200143)
  ·
    refine ⟨133210616452317486679800215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88807077634878324453200143 133210616452317486679800215)
    ·
      refine ⟨199815924678476230019700323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133210616452317486679800215 199815924678476230019700323)
      ·
        refine ⟨299723887017714345029550485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199815924678476230019700323 299723887017714345029550485)
        ·
          refine ⟨14049557203955359923260179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 299723887017714345029550485 14049557203955359923260179)
          ·
            refine ⟨21074335805933039884890269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14049557203955359923260179 21074335805933039884890269)
            ·
              refine ⟨7902875927224889956833851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21074335805933039884890269 7902875927224889956833851)
              ·
                refine ⟨11854313890837334935250777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7902875927224889956833851 11854313890837334935250777)
                ·
                  refine ⟨8890735418128001201438083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11854313890837334935250777 8890735418128001201438083)
                  ·
                    refine ⟨13336103127192001802157125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8890735418128001201438083 13336103127192001802157125)
                    ·
                      refine ⟨2500519336348500337904461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13336103127192001802157125 2500519336348500337904461)
                      ·
                        rfl

theorem cell23_4869744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 4].length) (baseStart_4869744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869744 prefixEnd_4869744 := by exact prefixLift 4869744
  have htrace : WordTrace (prefixWord ++ tailWord_4869744) baseStart_4869744 baseEnd_4869744 := by
    simpa [prefixWord, tailWord_4869744, baseEnd_4869744] using wordTrace_append hprefix tailTrace_4869744
  have hstable : (prefixWord ++ tailWord_4869744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869744).length < 2 ^ (prefixWord ++ tailWord_4869744).sum := by decide
  have hdescent : baseEnd_4869744 < baseStart_4869744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869757 : List Nat := [1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 6]
def baseStart_4869757 : Nat := 118140960795 + 4869757 * 2 ^ 59
def prefixEnd_4869757 : Nat := 4983230072969 + 3 ^ 40 * 4869757 * 2
def baseEnd_4869757 : Nat := 2500526011597008787041901

theorem tailTrace_4869757 : CollatzResearch.WordTrace tailWord_4869757 prefixEnd_4869757 2500526011597008787041901 := by
  unfold tailWord_4869757
  simp only [CollatzResearch.WordTrace]
  refine ⟨177614629418709552126623525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118409752945806368084415683 177614629418709552126623525)
  ·
    refine ⟨33302743016008041023741911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177614629418709552126623525 33302743016008041023741911)
    ·
      refine ⟨49954114524012061535612867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33302743016008041023741911 49954114524012061535612867)
      ·
        refine ⟨74931171786018092303419301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49954114524012061535612867 74931171786018092303419301)
        ·
          refine ⟨14049594709878392306891119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74931171786018092303419301 14049594709878392306891119)
          ·
            refine ⟨21074392064817588460336679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14049594709878392306891119 21074392064817588460336679)
            ·
              refine ⟨31611588097226382690505019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21074392064817588460336679 31611588097226382690505019)
              ·
                refine ⟨47417382145839574035757529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31611588097226382690505019 47417382145839574035757529)
                ·
                  refine ⟨35563036609379680526818147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47417382145839574035757529 35563036609379680526818147)
                  ·
                    refine ⟨53344554914069520790227221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35563036609379680526818147 53344554914069520790227221)
                    ·
                      refine ⟨2500526011597008787041901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53344554914069520790227221 2500526011597008787041901)
                      ·
                        rfl

theorem cell23_4869757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_4869757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869757 prefixEnd_4869757 := by exact prefixLift 4869757
  have htrace : WordTrace (prefixWord ++ tailWord_4869757) baseStart_4869757 baseEnd_4869757 := by
    simpa [prefixWord, tailWord_4869757, baseEnd_4869757] using wordTrace_append hprefix tailTrace_4869757
  have hstable : (prefixWord ++ tailWord_4869757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869757).length < 2 ^ (prefixWord ++ tailWord_4869757).sum := by decide
  have hdescent : baseEnd_4869757 < baseStart_4869757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869767 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 8]
def baseStart_4869767 : Nat := 118140960795 + 4869767 * 2 ^ 59
def prefixEnd_4869767 : Nat := 4983230072969 + 3 ^ 40 * 4869767 * 2
def baseEnd_4869767 : Nat := 277836794044839305324095

theorem tailTrace_4869767 : CollatzResearch.WordTrace tailWord_4869767 prefixEnd_4869767 277836794044839305324095 := by
  unfold tailWord_4869767
  simp only [CollatzResearch.WordTrace]
  refine ⟨177614994148673323834487555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118409996099115549222991703 177614994148673323834487555)
  ·
    refine ⟨266422491223009985751731333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177614994148673323834487555 266422491223009985751731333)
    ·
      refine ⟨49954217104314372328449625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266422491223009985751731333 49954217104314372328449625)
      ·
        refine ⟨37465662828235779246337219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49954217104314372328449625 37465662828235779246337219)
        ·
          refine ⟨56198494242353668869505829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37465662828235779246337219 56198494242353668869505829)
          ·
            refine ⟨10537217670441312913032343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56198494242353668869505829 10537217670441312913032343)
            ·
              refine ⟨15805826505661969369548515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10537217670441312913032343 15805826505661969369548515)
              ·
                refine ⟨23708739758492954054322773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15805826505661969369548515 23708739758492954054322773)
                ·
                  refine ⟨277836794044839305324095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23708739758492954054322773 277836794044839305324095)
                  ·
                    rfl

theorem cell23_4869767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 8].length) (baseStart_4869767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869767 prefixEnd_4869767 := by exact prefixLift 4869767
  have htrace : WordTrace (prefixWord ++ tailWord_4869767) baseStart_4869767 baseEnd_4869767 := by
    simpa [prefixWord, tailWord_4869767, baseEnd_4869767] using wordTrace_append hprefix tailTrace_4869767
  have hstable : (prefixWord ++ tailWord_4869767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869767).length < 2 ^ (prefixWord ++ tailWord_4869767).sum := by decide
  have hdescent : baseEnd_4869767 < baseStart_4869767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869797 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_4869797 : Nat := 118140960795 + 4869797 * 2 ^ 59
def prefixEnd_4869797 : Nat := 4983230072969 + 3 ^ 40 * 4869797 * 2
def baseEnd_4869797 : Nat := 833515516941062876847239

theorem tailTrace_4869797 : CollatzResearch.WordTrace tailWord_4869797 prefixEnd_4869797 833515516941062876847239 := by
  unfold tailWord_4869797
  simp only [CollatzResearch.WordTrace]
  refine ⟨177616088338564638958079645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118410725559043092638719763 177616088338564638958079645)
  ·
    refine ⟨66606033126961739609279867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177616088338564638958079645 66606033126961739609279867)
    ·
      refine ⟨99909049690442609413919801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66606033126961739609279867 99909049690442609413919801)
      ·
        refine ⟨74931787267831957060439851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99909049690442609413919801 74931787267831957060439851)
        ·
          refine ⟨112397680901747935590659777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74931787267831957060439851 112397680901747935590659777)
          ·
            refine ⟨84298260676310951692994833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112397680901747935590659777 84298260676310951692994833)
            ·
              refine ⟨63223695507233213769746125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84298260676310951692994833 63223695507233213769746125)
              ·
                refine ⟨23708885815212455163654797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63223695507233213769746125 23708885815212455163654797)
                ·
                  refine ⟨8890832180704670686370549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23708885815212455163654797 8890832180704670686370549)
                  ·
                    refine ⟨833515516941062876847239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8890832180704670686370549 833515516941062876847239)
                    ·
                      rfl

theorem cell23_4869797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_4869797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869797 prefixEnd_4869797 := by exact prefixLift 4869797
  have htrace : WordTrace (prefixWord ++ tailWord_4869797) baseStart_4869797 baseEnd_4869797 := by
    simpa [prefixWord, tailWord_4869797, baseEnd_4869797] using wordTrace_append hprefix tailTrace_4869797
  have hstable : (prefixWord ++ tailWord_4869797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869797).length < 2 ^ (prefixWord ++ tailWord_4869797).sum := by decide
  have hdescent : baseEnd_4869797 < baseStart_4869797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869804 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_4869804 : Nat := 118140960795 + 4869804 * 2 ^ 59
def prefixEnd_4869804 : Nat := 4983230072969 + 3 ^ 40 * 4869804 * 2
def baseEnd_4869804 : Nat := 2500550145187770103154185

theorem tailTrace_4869804 : CollatzResearch.WordTrace tailWord_4869804 prefixEnd_4869804 2500550145187770103154185 := by
  unfold tailWord_4869804
  simp only [CollatzResearch.WordTrace]
  refine ⟨88808171824769639576792233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118410895766359519435722977 88808171824769639576792233)
  ·
    refine ⟨66606128868577229682594175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88808171824769639576792233 66606128868577229682594175)
    ·
      refine ⟨99909193302865844523891263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66606128868577229682594175 99909193302865844523891263)
      ·
        refine ⟨149863789954298766785836895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99909193302865844523891263 149863789954298766785836895)
        ·
          refine ⟨224795684931448150178755343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149863789954298766785836895 224795684931448150178755343)
          ·
            refine ⟨337193527397172225268133015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224795684931448150178755343 337193527397172225268133015)
            ·
              refine ⟨505790291095758337902199523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337193527397172225268133015 505790291095758337902199523)
              ·
                refine ⟨758685436643637506853299285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505790291095758337902199523 758685436643637506853299285)
                ·
                  refine ⟨8890844960667627033437101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 758685436643637506853299285 8890844960667627033437101)
                  ·
                    refine ⟨3334066860250360137538913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8890844960667627033437101 3334066860250360137538913)
                    ·
                      refine ⟨2500550145187770103154185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334066860250360137538913 2500550145187770103154185)
                      ·
                        rfl

theorem cell23_4869804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_4869804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869804 prefixEnd_4869804 := by exact prefixLift 4869804
  have htrace : WordTrace (prefixWord ++ tailWord_4869804) baseStart_4869804 baseEnd_4869804 := by
    simpa [prefixWord, tailWord_4869804, baseEnd_4869804] using wordTrace_append hprefix tailTrace_4869804
  have hstable : (prefixWord ++ tailWord_4869804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869804).length < 2 ^ (prefixWord ++ tailWord_4869804).sum := by decide
  have hdescent : baseEnd_4869804 < baseStart_4869804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869821 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 2, 3, 2]
def baseStart_4869821 : Nat := 118140960795 + 4869821 * 2 ^ 59
def prefixEnd_4869821 : Nat := 4983230072969 + 3 ^ 40 * 4869821 * 2
def baseEnd_4869821 : Nat := 2500558874358896536641607

theorem tailTrace_4869821 : CollatzResearch.WordTrace tailWord_4869821 prefixEnd_4869821 2500558874358896536641607 := by
  unfold tailWord_4869821
  simp only [CollatzResearch.WordTrace]
  refine ⟨177616963690477691056953317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118411309126985127371302211 177616963690477691056953317)
  ·
    refine ⟨33303180691964567073178747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177616963690477691056953317 33303180691964567073178747)
    ·
      refine ⟨49954771037946850609768121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33303180691964567073178747 49954771037946850609768121)
      ·
        refine ⟨37466078278460137957326091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49954771037946850609768121 37466078278460137957326091)
        ·
          refine ⟨56199117417690206935989137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37466078278460137957326091 56199117417690206935989137)
          ·
            refine ⟨42149338063267655201991853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56199117417690206935989137 42149338063267655201991853)
            ·
              refine ⟨15806001773725370700746945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42149338063267655201991853 15806001773725370700746945)
              ·
                refine ⟨11854501330294028025560209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15806001773725370700746945 11854501330294028025560209)
                ·
                  refine ⟨8890875997720521019170157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11854501330294028025560209 8890875997720521019170157)
                  ·
                    refine ⟨3334078499145195382188809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8890875997720521019170157 3334078499145195382188809)
                    ·
                      refine ⟨2500558874358896536641607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334078499145195382188809 2500558874358896536641607)
                      ·
                        rfl

theorem cell23_4869821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_4869821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869821 prefixEnd_4869821 := by exact prefixLift 4869821
  have htrace : WordTrace (prefixWord ++ tailWord_4869821) baseStart_4869821 baseEnd_4869821 := by
    simpa [prefixWord, tailWord_4869821, baseEnd_4869821] using wordTrace_append hprefix tailTrace_4869821
  have hstable : (prefixWord ++ tailWord_4869821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869821).length < 2 ^ (prefixWord ++ tailWord_4869821).sum := by decide
  have hdescent : baseEnd_4869821 < baseStart_4869821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869847 : List Nat := [1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4869847 : Nat := 118140960795 + 4869847 * 2 ^ 59
def prefixEnd_4869847 : Nat := 4983230072969 + 3 ^ 40 * 4869847 * 2
def baseEnd_4869847 : Nat := 2500572224855913434916487

theorem tailTrace_4869847 : CollatzResearch.WordTrace tailWord_4869847 prefixEnd_4869847 2500572224855913434916487 := by
  unfold tailWord_4869847
  simp only [CollatzResearch.WordTrace]
  refine ⟨177617911988383497497399795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118411941325588998331599863 177617911988383497497399795)
  ·
    refine ⟨266426867982575246246099693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177617911988383497497399795 266426867982575246246099693)
    ·
      refine ⟨99910075493465717342287385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266426867982575246246099693 99910075493465717342287385)
      ·
        refine ⟨74932556620099288006715539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99910075493465717342287385 74932556620099288006715539)
        ·
          refine ⟨112398834930148932010073309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74932556620099288006715539 112398834930148932010073309)
          ·
            refine ⟨42149563098805849503777491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112398834930148932010073309 42149563098805849503777491)
            ·
              refine ⟨63224344648208774255666237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42149563098805849503777491 63224344648208774255666237)
              ·
                refine ⟨23709129243078290345874839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63224344648208774255666237 23709129243078290345874839)
                ·
                  refine ⟨35563693864617435518812259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23709129243078290345874839 35563693864617435518812259)
                  ·
                    refine ⟨53345540796926153278218389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35563693864617435518812259 53345540796926153278218389)
                    ·
                      refine ⟨2500572224855913434916487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53345540796926153278218389 2500572224855913434916487)
                      ·
                        rfl

theorem cell23_4869847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4869847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869847 prefixEnd_4869847 := by exact prefixLift 4869847
  have htrace : WordTrace (prefixWord ++ tailWord_4869847) baseStart_4869847 baseEnd_4869847 := by
    simpa [prefixWord, tailWord_4869847, baseEnd_4869847] using wordTrace_append hprefix tailTrace_4869847
  have hstable : (prefixWord ++ tailWord_4869847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869847).length < 2 ^ (prefixWord ++ tailWord_4869847).sum := by decide
  have hdescent : baseEnd_4869847 < baseStart_4869847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869864 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_4869864 : Nat := 118140960795 + 4869864 * 2 ^ 59
def prefixEnd_4869864 : Nat := 4983230072969 + 3 ^ 40 * 4869864 * 2
def baseEnd_4869864 : Nat := 2500580954027039868403909

theorem tailTrace_4869864 : CollatzResearch.WordTrace tailWord_4869864 prefixEnd_4869864 2500580954027039868403909 := by
  unfold tailWord_4869864
  simp only [CollatzResearch.WordTrace]
  refine ⟨88809266014660954700384323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118412354686214606267179097 88809266014660954700384323)
  ·
    refine ⟨133213899021991432050576485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88809266014660954700384323 133213899021991432050576485)
    ·
      refine ⟨24977606066623393509483091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133213899021991432050576485 24977606066623393509483091)
      ·
        refine ⟨37466409099935090264224637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24977606066623393509483091 37466409099935090264224637)
        ·
          refine ⟨14049903412475658849084239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37466409099935090264224637 14049903412475658849084239)
          ·
            refine ⟨21074855118713488273626359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14049903412475658849084239 21074855118713488273626359)
            ·
              refine ⟨31612282678070232410439539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21074855118713488273626359 31612282678070232410439539)
              ·
                refine ⟨47418424017105348615659309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31612282678070232410439539 47418424017105348615659309)
                ·
                  refine ⟨17781909006414505730872241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47418424017105348615659309 17781909006414505730872241)
                  ·
                    refine ⟨13336431754810879298154181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17781909006414505730872241 13336431754810879298154181)
                    ·
                      refine ⟨2500580954027039868403909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13336431754810879298154181 2500580954027039868403909)
                      ·
                        rfl

theorem cell23_4869864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_4869864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869864 prefixEnd_4869864 := by exact prefixLift 4869864
  have htrace : WordTrace (prefixWord ++ tailWord_4869864) baseStart_4869864 baseEnd_4869864 := by
    simpa [prefixWord, tailWord_4869864, baseEnd_4869864] using wordTrace_append hprefix tailTrace_4869864
  have hstable : (prefixWord ++ tailWord_4869864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869864).length < 2 ^ (prefixWord ++ tailWord_4869864).sum := by decide
  have hdescent : baseEnd_4869864 < baseStart_4869864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869878 : List Nat := [5, 1, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_4869878 : Nat := 118140960795 + 4869878 * 2 ^ 59
def prefixEnd_4869878 : Nat := 4983230072969 + 3 ^ 40 * 4869878 * 2
def baseEnd_4869878 : Nat := 833529380918734271209615

theorem tailTrace_4869878 : CollatzResearch.WordTrace tailWord_4869878 prefixEnd_4869878 833529380918734271209615 := by
  unfold tailWord_4869878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11101190165704449361986143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118412695100847459861185525 11101190165704449361986143)
  ·
    refine ⟨16651785248556674042979215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11101190165704449361986143 16651785248556674042979215)
    ·
      refine ⟨24977677872835011064468823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16651785248556674042979215 24977677872835011064468823)
      ·
        refine ⟨37466516809252516596703235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24977677872835011064468823 37466516809252516596703235)
        ·
          refine ⟨56199775213878774895054853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37466516809252516596703235 56199775213878774895054853)
          ·
            refine ⟨10537457852602270292822785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56199775213878774895054853 10537457852602270292822785)
            ·
              refine ⟨7903093389451702719617089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10537457852602270292822785 7903093389451702719617089)
              ·
                refine ⟨5927320042088777039712817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7903093389451702719617089 5927320042088777039712817)
                ·
                  refine ⟨4445490031566582779784613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5927320042088777039712817 4445490031566582779784613)
                  ·
                    refine ⟨833529380918734271209615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445490031566582779784613 833529380918734271209615)
                    ·
                      rfl

theorem cell23_4869878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_4869878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869878 prefixEnd_4869878 := by exact prefixLift 4869878
  have htrace : WordTrace (prefixWord ++ tailWord_4869878) baseStart_4869878 baseEnd_4869878 := by
    simpa [prefixWord, tailWord_4869878, baseEnd_4869878] using wordTrace_append hprefix tailTrace_4869878
  have hstable : (prefixWord ++ tailWord_4869878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869878).length < 2 ^ (prefixWord ++ tailWord_4869878).sum := by decide
  have hdescent : baseEnd_4869878 < baseStart_4869878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869884 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_4869884 : Nat := 118140960795 + 4869884 * 2 ^ 59
def prefixEnd_4869884 : Nat := 4983230072969 + 3 ^ 40 * 4869884 * 2
def baseEnd_4869884 : Nat := 2500591223640129790153817

theorem tailTrace_4869884 : CollatzResearch.WordTrace tailWord_4869884 prefixEnd_4869884 2500591223640129790153817 := by
  unfold tailWord_4869884
  simp only [CollatzResearch.WordTrace]
  refine ⟨88809630744624726408248353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118412840992832968544331137 88809630744624726408248353)
  ·
    refine ⟨66607223058468544806186265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88809630744624726408248353 66607223058468544806186265)
    ·
      refine ⟨49955417293851408604639699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66607223058468544806186265 49955417293851408604639699)
      ·
        refine ⟨74933125940777112906959549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49955417293851408604639699 74933125940777112906959549)
        ·
          refine ⟨28099922227791417340109831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74933125940777112906959549 28099922227791417340109831)
          ·
            refine ⟨42149883341687126010164747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28099922227791417340109831 42149883341687126010164747)
            ·
              refine ⟨63224825012530689015247121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42149883341687126010164747 63224825012530689015247121)
              ·
                refine ⟨47418618759398016761435341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63224825012530689015247121 47418618759398016761435341)
                ·
                  refine ⟨17781982034774256285538253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47418618759398016761435341 17781982034774256285538253)
                  ·
                    refine ⟨6668243263040346107076845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17781982034774256285538253 6668243263040346107076845)
                    ·
                      refine ⟨2500591223640129790153817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6668243263040346107076845 2500591223640129790153817)
                      ·
                        rfl

theorem cell23_4869884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_4869884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869884 prefixEnd_4869884 := by exact prefixLift 4869884
  have htrace : WordTrace (prefixWord ++ tailWord_4869884) baseStart_4869884 baseEnd_4869884 := by
    simpa [prefixWord, tailWord_4869884, baseEnd_4869884] using wordTrace_append hprefix tailTrace_4869884
  have hstable : (prefixWord ++ tailWord_4869884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869884).length < 2 ^ (prefixWord ++ tailWord_4869884).sum := by decide
  have hdescent : baseEnd_4869884 < baseStart_4869884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869887 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 2, 7]
def baseStart_4869887 : Nat := 118140960795 + 4869887 * 2 ^ 59
def prefixEnd_4869887 : Nat := 4983230072969 + 3 ^ 40 * 4869887 * 2
def baseEnd_4869887 : Nat := 833530921360697759472101

theorem tailTrace_4869887 : CollatzResearch.WordTrace tailWord_4869887 prefixEnd_4869887 833530921360697759472101 := by
  unfold tailWord_4869887
  simp only [CollatzResearch.WordTrace]
  refine ⟨177619370908238584328855915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118412913938825722885903943 177619370908238584328855915)
  ·
    refine ⟨266429056362357876493283873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177619370908238584328855915 266429056362357876493283873)
    ·
      refine ⟨199821792271768407369962905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266429056362357876493283873 199821792271768407369962905)
      ·
        refine ⟨149866344203826305527472179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199821792271768407369962905 149866344203826305527472179)
        ·
          refine ⟨224799516305739458291208269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149866344203826305527472179 224799516305739458291208269)
          ·
            refine ⟨84299818614652296859203101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224799516305739458291208269 84299818614652296859203101)
            ·
              refine ⟨31612431980494611322201163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84299818614652296859203101 31612431980494611322201163)
              ·
                refine ⟨47418647970741916983301745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31612431980494611322201163 47418647970741916983301745)
                ·
                  refine ⟨35563985978056437737476309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47418647970741916983301745 35563985978056437737476309)
                  ·
                    refine ⟨833530921360697759472101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35563985978056437737476309 833530921360697759472101)
                    ·
                      rfl

theorem cell23_4869887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_4869887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869887 prefixEnd_4869887 := by exact prefixLift 4869887
  have htrace : WordTrace (prefixWord ++ tailWord_4869887) baseStart_4869887 baseEnd_4869887 := by
    simpa [prefixWord, tailWord_4869887, baseEnd_4869887] using wordTrace_append hprefix tailTrace_4869887
  have hstable : (prefixWord ++ tailWord_4869887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869887).length < 2 ^ (prefixWord ++ tailWord_4869887).sum := by decide
  have hdescent : baseEnd_4869887 < baseStart_4869887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869897 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 5]
def baseStart_4869897 : Nat := 118140960795 + 4869897 * 2 ^ 59
def prefixEnd_4869897 : Nat := 4983230072969 + 3 ^ 40 * 4869897 * 2
def baseEnd_4869897 : Nat := 2500597898888638239291257

theorem tailTrace_4869897 : CollatzResearch.WordTrace tailWord_4869897 prefixEnd_4869897 2500597898888638239291257 := by
  unfold tailWord_4869897
  simp only [CollatzResearch.WordTrace]
  refine ⟨177619735638202356036719945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118413157092134904024479963 177619735638202356036719945)
  ·
    refine ⟨133214801728651767027539959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177619735638202356036719945 133214801728651767027539959)
    ·
      refine ⟨199822202592977650541309939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133214801728651767027539959 199822202592977650541309939)
      ·
        refine ⟨299733303889466475811964909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199822202592977650541309939 299733303889466475811964909)
        ·
          refine ⟨112399988958549928429486841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299733303889466475811964909 112399988958549928429486841)
          ·
            refine ⟨84299991718912446322115131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112399988958549928429486841 84299991718912446322115131)
            ·
              refine ⟨126449987578368669483172697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84299991718912446322115131 126449987578368669483172697)
              ·
                refine ⟨94837490683776502112379523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126449987578368669483172697 94837490683776502112379523)
                ·
                  refine ⟨142256236025664753168569285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94837490683776502112379523 142256236025664753168569285)
                  ·
                    refine ⟨26673044254812141219106741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142256236025664753168569285 26673044254812141219106741)
                    ·
                      refine ⟨2500597898888638239291257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26673044254812141219106741 2500597898888638239291257)
                      ·
                        rfl

theorem cell23_4869897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 4, 5].length) (baseStart_4869897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869897 prefixEnd_4869897 := by exact prefixLift 4869897
  have htrace : WordTrace (prefixWord ++ tailWord_4869897) baseStart_4869897 baseEnd_4869897 := by
    simpa [prefixWord, tailWord_4869897, baseEnd_4869897] using wordTrace_append hprefix tailTrace_4869897
  have hstable : (prefixWord ++ tailWord_4869897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869897).length < 2 ^ (prefixWord ++ tailWord_4869897).sum := by decide
  have hdescent : baseEnd_4869897 < baseStart_4869897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4869998 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_4869998 : Nat := 118140960795 + 4869998 * 2 ^ 59
def prefixEnd_4869998 : Nat := 4983230072969 + 3 ^ 40 * 4869998 * 2
def baseEnd_4869998 : Nat := 277849973381638038236477

theorem tailTrace_4869998 : CollatzResearch.WordTrace tailWord_4869998 prefixEnd_4869998 277849973381638038236477 := by
  unfold tailWord_4869998
  simp only [CollatzResearch.WordTrace]
  refine ⟨22202927426354556285768331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118415612940557633524097765 22202927426354556285768331)
  ·
    refine ⟨33304391139531834428652497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22202927426354556285768331 33304391139531834428652497)
    ·
      refine ⟨24978293354648875821489373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33304391139531834428652497 24978293354648875821489373)
      ·
        refine ⟨9366860007993328433058515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24978293354648875821489373 9366860007993328433058515)
        ·
          refine ⟨14050290011989992649587773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9366860007993328433058515 14050290011989992649587773)
          ·
            refine ⟨5268858754496247243595415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14050290011989992649587773 5268858754496247243595415)
            ·
              refine ⟨7903288131744370865393123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268858754496247243595415 7903288131744370865393123)
              ·
                refine ⟨11854932197616556298089685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7903288131744370865393123 11854932197616556298089685)
                ·
                  refine ⟨277849973381638038236477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11854932197616556298089685 277849973381638038236477)
                  ·
                    rfl

theorem cell23_4869998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_4869998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4869998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4869998 prefixEnd_4869998 := by exact prefixLift 4869998
  have htrace : WordTrace (prefixWord ++ tailWord_4869998) baseStart_4869998 baseEnd_4869998 := by
    simpa [prefixWord, tailWord_4869998, baseEnd_4869998] using wordTrace_append hprefix tailTrace_4869998
  have hstable : (prefixWord ++ tailWord_4869998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4869998).length < 2 ^ (prefixWord ++ tailWord_4869998).sum := by decide
  have hdescent : baseEnd_4869998 < baseStart_4869998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4869998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870001 : List Nat := [1, 2, 2, 2, 1, 3, 2, 1, 2, 5, 2]
def baseStart_4870001 : Nat := 118140960795 + 4870001 * 2 ^ 59
def prefixEnd_4870001 : Nat := 4983230072969 + 3 ^ 40 * 4870001 * 2
def baseEnd_4870001 : Nat := 2500651300876705832390779

theorem tailTrace_4870001 : CollatzResearch.WordTrace tailWord_4870001 prefixEnd_4870001 2500651300876705832390779 := by
  unfold tailWord_4870001
  simp only [CollatzResearch.WordTrace]
  refine ⟨177623528829825581798505857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118415685886550387865670571 177623528829825581798505857)
  ·
    refine ⟨133217646622369186348879393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177623528829825581798505857 133217646622369186348879393)
    ·
      refine ⟨99913234966776889761659545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133217646622369186348879393 99913234966776889761659545)
      ·
        refine ⟨74934926225082667321244659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99913234966776889761659545 74934926225082667321244659)
        ·
          refine ⟨112402389337624000981866989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74934926225082667321244659 112402389337624000981866989)
          ·
            refine ⟨42150896001609000368200121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112402389337624000981866989 42150896001609000368200121)
            ·
              refine ⟨31613172001206750276150091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42150896001609000368200121 31613172001206750276150091)
              ·
                refine ⟨47419758001810125414225137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31613172001206750276150091 47419758001810125414225137)
                ·
                  refine ⟨35564818501357594060668853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47419758001810125414225137 35564818501357594060668853)
                  ·
                    refine ⟨3334201734502274443187705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35564818501357594060668853 3334201734502274443187705)
                    ·
                      refine ⟨2500651300876705832390779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334201734502274443187705 2500651300876705832390779)
                      ·
                        rfl

theorem cell23_4870001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_4870001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870001 prefixEnd_4870001 := by exact prefixLift 4870001
  have htrace : WordTrace (prefixWord ++ tailWord_4870001) baseStart_4870001 baseEnd_4870001 := by
    simpa [prefixWord, tailWord_4870001, baseEnd_4870001] using wordTrace_append hprefix tailTrace_4870001
  have hstable : (prefixWord ++ tailWord_4870001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870001).length < 2 ^ (prefixWord ++ tailWord_4870001).sum := by decide
  have hdescent : baseEnd_4870001 < baseStart_4870001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870074 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_4870074 : Nat := 118140960795 + 4870074 * 2 ^ 59
def prefixEnd_4870074 : Nat := 4983230072969 + 3 ^ 40 * 4870074 * 2
def baseEnd_4870074 : Nat := 2500688784964484046777943

theorem tailTrace_4870074 : CollatzResearch.WordTrace tailWord_4870074 prefixEnd_4870074 2500688784964484046777943 := by
  unfold tailWord_4870074
  simp only [CollatzResearch.WordTrace]
  refine ⟨44406547839640278816478319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118417460905707410177275517 44406547839640278816478319)
  ·
    refine ⟨66609821759460418224717479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44406547839640278816478319 66609821759460418224717479)
    ·
      refine ⟨99914732639190627337076219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66609821759460418224717479 99914732639190627337076219)
      ·
        refine ⟨149872098958785941005614329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99914732639190627337076219 149872098958785941005614329)
        ·
          refine ⟨112404074219089455754210747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149872098958785941005614329 112404074219089455754210747)
          ·
            refine ⟨168606111328634183631316121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112404074219089455754210747 168606111328634183631316121)
            ·
              refine ⟨126454583496475637723487091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168606111328634183631316121 126454583496475637723487091)
              ·
                refine ⟨189681875244713456585230637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126454583496475637723487091 189681875244713456585230637)
                ·
                  refine ⟨71130703216767546219461489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189681875244713456585230637 71130703216767546219461489)
                  ·
                    refine ⟨53348027412575659664596117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71130703216767546219461489 53348027412575659664596117)
                    ·
                      refine ⟨2500688784964484046777943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53348027412575659664596117 2500688784964484046777943)
                      ·
                        rfl

theorem cell23_4870074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_4870074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870074 prefixEnd_4870074 := by exact prefixLift 4870074
  have htrace : WordTrace (prefixWord ++ tailWord_4870074) baseStart_4870074 baseEnd_4870074 := by
    simpa [prefixWord, tailWord_4870074, baseEnd_4870074] using wordTrace_append hprefix tailTrace_4870074
  have hstable : (prefixWord ++ tailWord_4870074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870074).length < 2 ^ (prefixWord ++ tailWord_4870074).sum := by decide
  have hdescent : baseEnd_4870074 < baseStart_4870074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870105 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 6]
def baseStart_4870105 : Nat := 118140960795 + 4870105 * 2 ^ 59
def prefixEnd_4870105 : Nat := 4983230072969 + 3 ^ 40 * 4870105 * 2
def baseEnd_4870105 : Nat := 277856078096085936165589

theorem tailTrace_4870105 : CollatzResearch.WordTrace tailWord_4870105 prefixEnd_4870105 277856078096085936165589 := by
  unfold tailWord_4870105
  simp only [CollatzResearch.WordTrace]
  refine ⟨177627322021448807560291769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118418214680965871706861179 177627322021448807560291769)
  ·
    refine ⟨133220491516086605670218827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177627322021448807560291769 133220491516086605670218827)
    ·
      refine ⟨199830737274129908505328241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133220491516086605670218827 199830737274129908505328241)
      ·
        refine ⟨149873052955597431378996181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199830737274129908505328241 149873052955597431378996181)
        ·
          refine ⟨3512649678646814797945223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149873052955597431378996181 3512649678646814797945223)
          ·
            refine ⟨5268974517970222196917835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512649678646814797945223 5268974517970222196917835)
            ·
              refine ⟨7903461776955333295376753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5268974517970222196917835 7903461776955333295376753)
              ·
                refine ⟨5927596332716499971532565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7903461776955333295376753 5927596332716499971532565)
                ·
                  refine ⟨277856078096085936165589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5927596332716499971532565 277856078096085936165589)
                  ·
                    rfl

theorem cell23_4870105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 6].length) (baseStart_4870105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870105 prefixEnd_4870105 := by exact prefixLift 4870105
  have htrace : WordTrace (prefixWord ++ tailWord_4870105) baseStart_4870105 baseEnd_4870105 := by
    simpa [prefixWord, tailWord_4870105, baseEnd_4870105] using wordTrace_append hprefix tailTrace_4870105
  have hstable : (prefixWord ++ tailWord_4870105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870105).length < 2 ^ (prefixWord ++ tailWord_4870105).sum := by decide
  have hdescent : baseEnd_4870105 < baseStart_4870105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870115 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4870115 : Nat := 118140960795 + 4870115 * 2 ^ 59
def prefixEnd_4870115 : Nat := 4983230072969 + 3 ^ 40 * 4870115 * 2
def baseEnd_4870115 : Nat := 2500709837671318386365255

theorem tailTrace_4870115 : CollatzResearch.WordTrace tailWord_4870115 prefixEnd_4870115 2500709837671318386365255 := by
  unfold tailWord_4870115
  simp only [CollatzResearch.WordTrace]
  refine ⟨177627686751412579268155799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118418457834275052845437199 177627686751412579268155799)
  ·
    refine ⟨266441530127118868902233699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177627686751412579268155799 266441530127118868902233699)
    ·
      refine ⟨399662295190678303353350549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266441530127118868902233699 399662295190678303353350549)
      ·
        refine ⟨18734170087063045469688307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 399662295190678303353350549 18734170087063045469688307)
        ·
          refine ⟨28101255130594568204532461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18734170087063045469688307 28101255130594568204532461)
          ·
            refine ⟨10537970673972963076699673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28101255130594568204532461 10537970673972963076699673)
            ·
              refine ⟨7903478005479722307524755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10537970673972963076699673 7903478005479722307524755)
              ·
                refine ⟨11855217008219583461287133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7903478005479722307524755 11855217008219583461287133)
                ·
                  refine ⟨4445706378082343797982675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11855217008219583461287133 4445706378082343797982675)
                  ·
                    refine ⟨6668559567123515696974013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4445706378082343797982675 6668559567123515696974013)
                    ·
                      refine ⟨2500709837671318386365255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6668559567123515696974013 2500709837671318386365255)
                      ·
                        rfl

theorem cell23_4870115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4870115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870115 prefixEnd_4870115 := by exact prefixLift 4870115
  have htrace : WordTrace (prefixWord ++ tailWord_4870115) baseStart_4870115 baseEnd_4870115 := by
    simpa [prefixWord, tailWord_4870115, baseEnd_4870115] using wordTrace_append hprefix tailTrace_4870115
  have hstable : (prefixWord ++ tailWord_4870115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870115).length < 2 ^ (prefixWord ++ tailWord_4870115).sum := by decide
  have hdescent : baseEnd_4870115 < baseStart_4870115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870158 : List Nat := [4, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5]
def baseStart_4870158 : Nat := 118140960795 + 4870158 * 2 ^ 59
def prefixEnd_4870158 : Nat := 4983230072969 + 3 ^ 40 * 4870158 * 2
def baseEnd_4870158 : Nat := 2500731917339461718127557

theorem tailTrace_4870158 : CollatzResearch.WordTrace tailWord_4870158 prefixEnd_4870158 2500731917339461718127557 := by
  unfold tailWord_4870158
  simp only [CollatzResearch.WordTrace]
  refine ⟨22203656886282099701496391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118419503393504531741314085 22203656886282099701496391)
  ·
    refine ⟨33305485329423149552244587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22203656886282099701496391 33305485329423149552244587)
    ·
      refine ⟨49958227994134724328366881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33305485329423149552244587 49958227994134724328366881)
      ·
        refine ⟨37468670995601043246275161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49958227994134724328366881 37468670995601043246275161)
        ·
          refine ⟨28101503246700782434706371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37468670995601043246275161 28101503246700782434706371)
          ·
            refine ⟨42152254870051173652059557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28101503246700782434706371 42152254870051173652059557)
            ·
              refine ⟨7903547788134595059761167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42152254870051173652059557 7903547788134595059761167)
              ·
                refine ⟨11855321682201892589641751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7903547788134595059761167 11855321682201892589641751)
                ·
                  refine ⟨17782982523302838884462627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11855321682201892589641751 17782982523302838884462627)
                  ·
                    refine ⟨26674473784954258326693941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17782982523302838884462627 26674473784954258326693941)
                    ·
                      refine ⟨2500731917339461718127557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26674473784954258326693941 2500731917339461718127557)
                      ·
                        rfl

theorem cell23_4870158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 1, 1, 1, 5].length) (baseStart_4870158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870158 prefixEnd_4870158 := by exact prefixLift 4870158
  have htrace : WordTrace (prefixWord ++ tailWord_4870158) baseStart_4870158 baseEnd_4870158 := by
    simpa [prefixWord, tailWord_4870158, baseEnd_4870158] using wordTrace_append hprefix tailTrace_4870158
  have hstable : (prefixWord ++ tailWord_4870158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870158).length < 2 ^ (prefixWord ++ tailWord_4870158).sum := by decide
  have hdescent : baseEnd_4870158 < baseStart_4870158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870171 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3]
def baseStart_4870171 : Nat := 118140960795 + 4870171 * 2 ^ 59
def prefixEnd_4870171 : Nat := 4983230072969 + 3 ^ 40 * 4870171 * 2
def baseEnd_4870171 : Nat := 2500738592587970167264997

theorem tailTrace_4870171 : CollatzResearch.WordTrace tailWord_4870171 prefixEnd_4870171 2500738592587970167264997 := by
  unfold tailWord_4870171
  simp only [CollatzResearch.WordTrace]
  refine ⟨177629729239209700832194367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118419819492806467221462911 177629729239209700832194367)
  ·
    refine ⟨266444593858814551248291551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177629729239209700832194367 266444593858814551248291551)
    ·
      refine ⟨399666890788221826872437327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266444593858814551248291551 399666890788221826872437327)
      ·
        refine ⟨599500336182332740308655991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399666890788221826872437327 599500336182332740308655991)
        ·
          refine ⟨899250504273499110462983987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599500336182332740308655991 899250504273499110462983987)
          ·
            refine ⟨1348875756410248665694475981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899250504273499110462983987 1348875756410248665694475981)
            ·
              refine ⟨505828408653843249635428493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1348875756410248665694475981 505828408653843249635428493)
              ·
                refine ⟨189685653245191218613285685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 505828408653843249635428493 189685653245191218613285685)
                ·
                  refine ⟨17783029991736676744995533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 189685653245191218613285685 17783029991736676744995533)
                  ·
                    refine ⟨6668636246901253779373325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17783029991736676744995533 6668636246901253779373325)
                    ·
                      refine ⟨2500738592587970167264997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6668636246901253779373325 2500738592587970167264997)
                      ·
                        rfl

theorem cell23_4870171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 3].length) (baseStart_4870171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870171 prefixEnd_4870171 := by exact prefixLift 4870171
  have htrace : WordTrace (prefixWord ++ tailWord_4870171) baseStart_4870171 baseEnd_4870171 := by
    simpa [prefixWord, tailWord_4870171, baseEnd_4870171] using wordTrace_append hprefix tailTrace_4870171
  have hstable : (prefixWord ++ tailWord_4870171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870171).length < 2 ^ (prefixWord ++ tailWord_4870171).sum := by decide
  have hdescent : baseEnd_4870171 < baseStart_4870171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870172 : List Nat := [2, 2, 3, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_4870172 : Nat := 118140960795 + 4870172 * 2 ^ 59
def prefixEnd_4870172 : Nat := 4983230072969 + 3 ^ 40 * 4870172 * 2
def baseEnd_4870172 : Nat := 2500739106068624663352493

theorem tailTrace_4870172 : CollatzResearch.WordTrace tailWord_4870172 prefixEnd_4870172 2500739106068624663352493 := by
  unfold tailWord_4870172
  simp only [CollatzResearch.WordTrace]
  refine ⟨88814882856103039001490385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118419843808137385335320513 88814882856103039001490385)
  ·
    refine ⟨66611162142077279251117789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88814882856103039001490385 66611162142077279251117789)
    ·
      refine ⟨24979185803278979719169171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66611162142077279251117789 24979185803278979719169171)
      ·
        refine ⟨37468778704918469578753757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24979185803278979719169171 37468778704918469578753757)
        ·
          refine ⟨14050792014344426092032659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37468778704918469578753757 14050792014344426092032659)
          ·
            refine ⟨21076188021516639138048989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14050792014344426092032659 21076188021516639138048989)
            ·
              refine ⟨7903570508068739676768371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21076188021516639138048989 7903570508068739676768371)
              ·
                refine ⟨11855355762103109515152557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7903570508068739676768371 11855355762103109515152557)
                ·
                  refine ⟨4445758410788666068182209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11855355762103109515152557 4445758410788666068182209)
                  ·
                    refine ⟨3334318808091499551136657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4445758410788666068182209 3334318808091499551136657)
                    ·
                      refine ⟨2500739106068624663352493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334318808091499551136657 2500739106068624663352493)
                      ·
                        rfl

theorem cell23_4870172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_4870172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870172 prefixEnd_4870172 := by exact prefixLift 4870172
  have htrace : WordTrace (prefixWord ++ tailWord_4870172) baseStart_4870172 baseEnd_4870172 := by
    simpa [prefixWord, tailWord_4870172, baseEnd_4870172] using wordTrace_append hprefix tailTrace_4870172
  have hstable : (prefixWord ++ tailWord_4870172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870172).length < 2 ^ (prefixWord ++ tailWord_4870172).sum := by decide
  have hdescent : baseEnd_4870172 < baseStart_4870172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870188 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_4870188 : Nat := 118140960795 + 4870188 * 2 ^ 59
def prefixEnd_4870188 : Nat := 4983230072969 + 3 ^ 40 * 4870188 * 2
def baseEnd_4870188 : Nat := 2500747321759096600752419

theorem tailTrace_4870188 : CollatzResearch.WordTrace tailWord_4870188 prefixEnd_4870188 2500747321759096600752419 := by
  unfold tailWord_4870188
  simp only [CollatzResearch.WordTrace]
  refine ⟨88815174640074056367781609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118420232853432075157042145 88815174640074056367781609)
  ·
    refine ⟨66611380980055542275836207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88815174640074056367781609 66611380980055542275836207)
    ·
      refine ⟨99917071470083313413754311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66611380980055542275836207 99917071470083313413754311)
      ·
        refine ⟨149875607205124970120631467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99917071470083313413754311 149875607205124970120631467)
        ·
          refine ⟨224813410807687455180947201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149875607205124970120631467 224813410807687455180947201)
          ·
            refine ⟨168610058105765591385710401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224813410807687455180947201 168610058105765591385710401)
            ·
              refine ⟨126457543579324193539282801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168610058105765591385710401 126457543579324193539282801)
              ·
                refine ⟨94843157684493145154462101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126457543579324193539282801 94843157684493145154462101)
                ·
                  refine ⟨4445773016460616179115411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94843157684493145154462101 4445773016460616179115411)
                  ·
                    refine ⟨6668659524690924268673117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4445773016460616179115411 6668659524690924268673117)
                    ·
                      refine ⟨2500747321759096600752419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6668659524690924268673117 2500747321759096600752419)
                      ·
                        rfl

theorem cell23_4870188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_4870188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870188 prefixEnd_4870188 := by exact prefixLift 4870188
  have htrace : WordTrace (prefixWord ++ tailWord_4870188) baseStart_4870188 baseEnd_4870188 := by
    simpa [prefixWord, tailWord_4870188, baseEnd_4870188] using wordTrace_append hprefix tailTrace_4870188
  have hstable : (prefixWord ++ tailWord_4870188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870188).length < 2 ^ (prefixWord ++ tailWord_4870188).sum := by decide
  have hdescent : baseEnd_4870188 < baseStart_4870188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870222 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3]
def baseStart_4870222 : Nat := 118140960795 + 4870222 * 2 ^ 59
def prefixEnd_4870222 : Nat := 4983230072969 + 3 ^ 40 * 4870222 * 2
def baseEnd_4870222 : Nat := 2500764780101349467727263

theorem tailTrace_4870222 : CollatzResearch.WordTrace tailWord_4870222 prefixEnd_4870222 2500764780101349467727263 := by
  unfold tailWord_4870222
  simp only [CollatzResearch.WordTrace]
  refine ⟨22203948670253117067787615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118421059574683291028200613 22203948670253117067787615)
  ·
    refine ⟨33305923005379675601681423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22203948670253117067787615 33305923005379675601681423)
    ·
      refine ⟨49958884508069513402522135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33305923005379675601681423 49958884508069513402522135)
      ·
        refine ⟨74938326762104270103783203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49958884508069513402522135 74938326762104270103783203)
        ·
          refine ⟨112407490143156405155674805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74938326762104270103783203 112407490143156405155674805)
          ·
            refine ⟨10538202200920912983344513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112407490143156405155674805 10538202200920912983344513)
            ·
              refine ⟨7903651650690684737508385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10538202200920912983344513 7903651650690684737508385)
              ·
                refine ⟨5927738738018013553131289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7903651650690684737508385 5927738738018013553131289)
                ·
                  refine ⟨4445804053513510164848467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5927738738018013553131289 4445804053513510164848467)
                  ·
                    refine ⟨6668706080270265247272701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4445804053513510164848467 6668706080270265247272701)
                    ·
                      refine ⟨2500764780101349467727263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6668706080270265247272701 2500764780101349467727263)
                      ·
                        rfl

theorem cell23_4870222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 2, 1, 3].length) (baseStart_4870222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870222 prefixEnd_4870222 := by exact prefixLift 4870222
  have htrace : WordTrace (prefixWord ++ tailWord_4870222) baseStart_4870222 baseEnd_4870222 := by
    simpa [prefixWord, tailWord_4870222, baseEnd_4870222] using wordTrace_append hprefix tailTrace_4870222
  have hstable : (prefixWord ++ tailWord_4870222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870222).length < 2 ^ (prefixWord ++ tailWord_4870222).sum := by decide
  have hdescent : baseEnd_4870222 < baseStart_4870222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870231 : List Nat := [1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4870231 : Nat := 118140960795 + 4870231 * 2 ^ 59
def prefixEnd_4870231 : Nat := 4983230072969 + 3 ^ 40 * 4870231 * 2
def baseEnd_4870231 : Nat := 2500769401427239932514721

theorem tailTrace_4870231 : CollatzResearch.WordTrace tailWord_4870231 prefixEnd_4870231 2500769401427239932514721 := by
  unfold tailWord_4870231
  simp only [CollatzResearch.WordTrace]
  refine ⟨177631917618992331079378547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118421278412661554052919031 177631917618992331079378547)
  ·
    refine ⟨266447876428488496619067821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177631917618992331079378547 266447876428488496619067821)
    ·
      refine ⟨99917953660683186232150433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266447876428488496619067821 99917953660683186232150433)
      ·
        refine ⟨74938465245512389674112825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99917953660683186232150433 74938465245512389674112825)
        ·
          refine ⟨56203848934134292255584619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74938465245512389674112825 56203848934134292255584619)
          ·
            refine ⟨84305773401201438383376929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56203848934134292255584619 84305773401201438383376929)
            ·
              refine ⟨63229330050901078787532697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84305773401201438383376929 63229330050901078787532697)
              ·
                refine ⟨47421997538175809090649523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63229330050901078787532697 47421997538175809090649523)
                ·
                  refine ⟨71132996307263713635974285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47421997538175809090649523 71132996307263713635974285)
                  ·
                    refine ⟨26674873615223892613490357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71132996307263713635974285 26674873615223892613490357)
                    ·
                      refine ⟨2500769401427239932514721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26674873615223892613490357 2500769401427239932514721)
                      ·
                        rfl

theorem cell23_4870231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4870231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870231 prefixEnd_4870231 := by exact prefixLift 4870231
  have htrace : WordTrace (prefixWord ++ tailWord_4870231) baseStart_4870231 baseEnd_4870231 := by
    simpa [prefixWord, tailWord_4870231, baseEnd_4870231] using wordTrace_append hprefix tailTrace_4870231
  have hstable : (prefixWord ++ tailWord_4870231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870231).length < 2 ^ (prefixWord ++ tailWord_4870231).sum := by decide
  have hdescent : baseEnd_4870231 < baseStart_4870231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870245 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 1, 4, 2]
def baseStart_4870245 : Nat := 118140960795 + 4870245 * 2 ^ 59
def prefixEnd_4870245 : Nat := 4983230072969 + 3 ^ 40 * 4870245 * 2
def baseEnd_4870245 : Nat := 2500776590156402877739657

theorem tailTrace_4870245 : CollatzResearch.WordTrace tailWord_4870245 prefixEnd_4870245 2500776590156402877739657 := by
  unfold tailWord_4870245
  simp only [CollatzResearch.WordTrace]
  refine ⟨177632428240941611470388189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118421618827294407646925459 177632428240941611470388189)
  ·
    refine ⟨66612160590353104301395571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177632428240941611470388189 66612160590353104301395571)
    ·
      refine ⟨99918240885529656452093357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66612160590353104301395571 99918240885529656452093357)
      ·
        refine ⟨37469340332073621169535009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99918240885529656452093357 37469340332073621169535009)
        ·
          refine ⟨28102005249055215877151257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37469340332073621169535009 28102005249055215877151257)
          ·
            refine ⟨21076503936791411907863443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28102005249055215877151257 21076503936791411907863443)
            ·
              refine ⟨31614755905187117861795165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21076503936791411907863443 31614755905187117861795165)
              ·
                refine ⟨11855533464445169198173187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31614755905187117861795165 11855533464445169198173187)
                ·
                  refine ⟨17783300196667753797259781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11855533464445169198173187 17783300196667753797259781)
                  ·
                    refine ⟨3334368786875203836986209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17783300196667753797259781 3334368786875203836986209)
                    ·
                      refine ⟨2500776590156402877739657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334368786875203836986209 2500776590156402877739657)
                      ·
                        rfl

theorem cell23_4870245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 1, 4, 2].length) (baseStart_4870245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870245 prefixEnd_4870245 := by exact prefixLift 4870245
  have htrace : WordTrace (prefixWord ++ tailWord_4870245) baseStart_4870245 baseEnd_4870245 := by
    simpa [prefixWord, tailWord_4870245, baseEnd_4870245] using wordTrace_append hprefix tailTrace_4870245
  have hstable : (prefixWord ++ tailWord_4870245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870245).length < 2 ^ (prefixWord ++ tailWord_4870245).sum := by decide
  have hdescent : baseEnd_4870245 < baseStart_4870245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870262 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_4870262 : Nat := 118140960795 + 4870262 * 2 ^ 59
def prefixEnd_4870262 : Nat := 4983230072969 + 3 ^ 40 * 4870262 * 2
def baseEnd_4870262 : Nat := 2500785319327529311227079

theorem tailTrace_4870262 : CollatzResearch.WordTrace tailWord_4870262 prefixEnd_4870262 2500785319327529311227079 := by
  unfold tailWord_4870262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11102065517617501460859815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118422032187920015582504693 11102065517617501460859815)
  ·
    refine ⟨16653098276426252191289723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11102065517617501460859815 16653098276426252191289723)
    ·
      refine ⟨24979647414639378286934585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16653098276426252191289723 24979647414639378286934585)
      ·
        refine ⟨18734735560979533715200939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24979647414639378286934585 18734735560979533715200939)
        ·
          refine ⟨28102103341469300572801409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18734735560979533715200939 28102103341469300572801409)
          ·
            refine ⟨21076577506101975429601057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28102103341469300572801409 21076577506101975429601057)
            ·
              refine ⟨15807433129576481572200793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21076577506101975429601057 15807433129576481572200793)
              ·
                refine ⟨11855574847182361179150595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15807433129576481572200793 11855574847182361179150595)
                ·
                  refine ⟨17783362270773541768725893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11855574847182361179150595 17783362270773541768725893)
                  ·
                    refine ⟨3334380425770039081636105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17783362270773541768725893 3334380425770039081636105)
                    ·
                      refine ⟨2500785319327529311227079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334380425770039081636105 2500785319327529311227079)
                      ·
                        rfl

theorem cell23_4870262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_4870262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870262 prefixEnd_4870262 := by exact prefixLift 4870262
  have htrace : WordTrace (prefixWord ++ tailWord_4870262) baseStart_4870262 baseEnd_4870262 := by
    simpa [prefixWord, tailWord_4870262, baseEnd_4870262] using wordTrace_append hprefix tailTrace_4870262
  have hstable : (prefixWord ++ tailWord_4870262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870262).length < 2 ^ (prefixWord ++ tailWord_4870262).sum := by decide
  have hdescent : baseEnd_4870262 < baseStart_4870262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870291 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7]
def baseStart_4870291 : Nat := 118140960795 + 4870291 * 2 ^ 59
def prefixEnd_4870291 : Nat := 4983230072969 + 3 ^ 40 * 4870291 * 2
def baseEnd_4870291 : Nat := 2500800210266509697764445

theorem tailTrace_4870291 : CollatzResearch.WordTrace tailWord_4870291 prefixEnd_4870291 2500800210266509697764445 := by
  unfold tailWord_4870291
  simp only [CollatzResearch.WordTrace]
  refine ⟨177634105998774961326562727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118422737332516640884375151 177634105998774961326562727)
  ·
    refine ⟨266451158998162441989844091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177634105998774961326562727 266451158998162441989844091)
    ·
      refine ⟨399676738497243662984766137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266451158998162441989844091 399676738497243662984766137)
      ·
        refine ⟨299757553872932747238574603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399676738497243662984766137 299757553872932747238574603)
        ·
          refine ⟨449636330809399120857861905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299757553872932747238574603 449636330809399120857861905)
          ·
            refine ⟨337227248107049340643396429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449636330809399120857861905 337227248107049340643396429)
            ·
              refine ⟨126460218040143502741273661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337227248107049340643396429 126460218040143502741273661)
              ·
                refine ⟨47422581765053813527977623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126460218040143502741273661 47422581765053813527977623)
                ·
                  refine ⟨71133872647580720291966435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47422581765053813527977623 71133872647580720291966435)
                  ·
                    refine ⟨106700808971371080437949653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71133872647580720291966435 106700808971371080437949653)
                    ·
                      refine ⟨2500800210266509697764445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 106700808971371080437949653 2500800210266509697764445)
                      ·
                        rfl

theorem cell23_4870291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_4870291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870291 prefixEnd_4870291 := by exact prefixLift 4870291
  have htrace : WordTrace (prefixWord ++ tailWord_4870291) baseStart_4870291 baseEnd_4870291 := by
    simpa [prefixWord, tailWord_4870291, baseEnd_4870291] using wordTrace_append hprefix tailTrace_4870291
  have hstable : (prefixWord ++ tailWord_4870291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870291).length < 2 ^ (prefixWord ++ tailWord_4870291).sum := by decide
  have hdescent : baseEnd_4870291 < baseStart_4870291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870296 : List Nat := [2, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2]
def baseStart_4870296 : Nat := 118140960795 + 4870296 * 2 ^ 59
def prefixEnd_4870296 : Nat := 4983230072969 + 3 ^ 40 * 4870296 * 2
def baseEnd_4870296 : Nat := 2500802777669782178201923

theorem tailTrace_4870296 : CollatzResearch.WordTrace tailWord_4870296 prefixEnd_4870296 2500802777669782178201923 := by
  unfold tailWord_4870296
  simp only [CollatzResearch.WordTrace]
  refine ⟨88817144181878423590247371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118422858909171231453663161 88817144181878423590247371)
  ·
    refine ⟨133225716272817635385371057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88817144181878423590247371 133225716272817635385371057)
    ·
      refine ⟨99919287204613226539028293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133225716272817635385371057 99919287204613226539028293)
      ·
        refine ⟨18734866350864979976067805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99919287204613226539028293 18734866350864979976067805)
        ·
          refine ⟨7025574881574367491025427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18734866350864979976067805 7025574881574367491025427)
          ·
            refine ⟨10538362322361551236538141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7025574881574367491025427 10538362322361551236538141)
            ·
              refine ⟨3951885870885581713701803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10538362322361551236538141 3951885870885581713701803)
              ·
                refine ⟨5927828806328372570552705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3951885870885581713701803 5927828806328372570552705)
                ·
                  refine ⟨4445871604746279427914529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5927828806328372570552705 4445871604746279427914529)
                  ·
                    refine ⟨3334403703559709570935897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4445871604746279427914529 3334403703559709570935897)
                    ·
                      refine ⟨2500802777669782178201923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334403703559709570935897 2500802777669782178201923)
                      ·
                        rfl

theorem cell23_4870296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_4870296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870296 prefixEnd_4870296 := by exact prefixLift 4870296
  have htrace : WordTrace (prefixWord ++ tailWord_4870296) baseStart_4870296 baseEnd_4870296 := by
    simpa [prefixWord, tailWord_4870296, baseEnd_4870296] using wordTrace_append hprefix tailTrace_4870296
  have hstable : (prefixWord ++ tailWord_4870296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870296).length < 2 ^ (prefixWord ++ tailWord_4870296).sum := by decide
  have hdescent : baseEnd_4870296 < baseStart_4870296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870396 : List Nat := [2, 2, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_4870396 : Nat := 118140960795 + 4870396 * 2 ^ 59
def prefixEnd_4870396 : Nat := 4983230072969 + 3 ^ 40 * 4870396 * 2
def baseEnd_4870396 : Nat := 833618041911743928983821

theorem tailTrace_4870396 : CollatzResearch.WordTrace tailWord_4870396 prefixEnd_4870396 833618041911743928983821 := by
  unfold tailWord_4870396
  simp only [CollatzResearch.WordTrace]
  refine ⟨88818967831697282129567521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118425290442263042839423361 88818967831697282129567521)
  ·
    refine ⟨66614225873772961597175641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88818967831697282129567521 66614225873772961597175641)
    ·
      refine ⟨49960669405329721197881731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66614225873772961597175641 49960669405329721197881731)
      ·
        refine ⟨74941004107994581796822597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49960669405329721197881731 74941004107994581796822597)
        ·
          refine ⟨14051438270248984086904237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74941004107994581796822597 14051438270248984086904237)
          ·
            refine ⟨5269289351343369032589089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14051438270248984086904237 5269289351343369032589089)
            ·
              refine ⟨3951967013507526774441817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5269289351343369032589089 3951967013507526774441817)
              ·
                refine ⟨2963975260130645080831363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3951967013507526774441817 2963975260130645080831363)
                ·
                  refine ⟨4445962890195967621247045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963975260130645080831363 4445962890195967621247045)
                  ·
                    refine ⟨833618041911743928983821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445962890195967621247045 833618041911743928983821)
                    ·
                      rfl

theorem cell23_4870396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_4870396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870396 prefixEnd_4870396 := by exact prefixLift 4870396
  have htrace : WordTrace (prefixWord ++ tailWord_4870396) baseStart_4870396 baseEnd_4870396 := by
    simpa [prefixWord, tailWord_4870396, baseEnd_4870396] using wordTrace_append hprefix tailTrace_4870396
  have hstable : (prefixWord ++ tailWord_4870396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870396).length < 2 ^ (prefixWord ++ tailWord_4870396).sum := by decide
  have hdescent : baseEnd_4870396 < baseStart_4870396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870429 : List Nat := [1, 4, 2, 3, 2, 1, 1, 1, 1, 5, 2]
def baseStart_4870429 : Nat := 118140960795 + 4870429 * 2 ^ 59
def prefixEnd_4870429 : Nat := 4983230072969 + 3 ^ 40 * 4870429 * 2
def baseEnd_4870429 : Nat := 2500871070596830157838811

theorem tailTrace_4870429 : CollatzResearch.WordTrace tailWord_4870429 prefixEnd_4870429 2500871070596830157838811 := by
  unfold tailWord_4870429
  simp only [CollatzResearch.WordTrace]
  refine ⟨177639139272275010895086341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118426092848183340596724227 177639139272275010895086341)
  ·
    refine ⟨33307338613551564542828689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177639139272275010895086341 33307338613551564542828689)
    ·
      refine ⟨24980503960163673407121517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33307338613551564542828689 24980503960163673407121517)
      ·
        refine ⟨9367688985061377527670569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24980503960163673407121517 9367688985061377527670569)
        ·
          refine ⟨7025766738796033145752927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9367688985061377527670569 7025766738796033145752927)
          ·
            refine ⟨10538650108194049718629391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7025766738796033145752927 10538650108194049718629391)
            ·
              refine ⟨15807975162291074577944087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10538650108194049718629391 15807975162291074577944087)
              ·
                refine ⟨23711962743436611866916131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15807975162291074577944087 23711962743436611866916131)
                ·
                  refine ⟨35567944115154917800374197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23711962743436611866916131 35567944115154917800374197)
                  ·
                    refine ⟨3334494760795773543785081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35567944115154917800374197 3334494760795773543785081)
                    ·
                      refine ⟨2500871070596830157838811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334494760795773543785081 2500871070596830157838811)
                      ·
                        rfl

theorem cell23_4870429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_4870429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870429 prefixEnd_4870429 := by exact prefixLift 4870429
  have htrace : WordTrace (prefixWord ++ tailWord_4870429) baseStart_4870429 baseEnd_4870429 := by
    simpa [prefixWord, tailWord_4870429, baseEnd_4870429] using wordTrace_append hprefix tailTrace_4870429
  have hstable : (prefixWord ++ tailWord_4870429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870429).length < 2 ^ (prefixWord ++ tailWord_4870429).sum := by decide
  have hdescent : baseEnd_4870429 < baseStart_4870429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870435 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 4, 4]
def baseStart_4870435 : Nat := 118140960795 + 4870435 * 2 ^ 59
def prefixEnd_4870435 : Nat := 4983230072969 + 3 ^ 40 * 4870435 * 2
def baseEnd_4870435 : Nat := 833624717160252378121261

theorem tailTrace_4870435 : CollatzResearch.WordTrace tailWord_4870435 prefixEnd_4870435 833624717160252378121261 := by
  unfold tailWord_4870435
  simp only [CollatzResearch.WordTrace]
  refine ⟨177639358110253273919804759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118426238740168849279869839 177639358110253273919804759)
  ·
    refine ⟨266459037165379910879707139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177639358110253273919804759 266459037165379910879707139)
    ·
      refine ⟨399688555748069866319560709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266459037165379910879707139 399688555748069866319560709)
      ·
        refine ⟨74941604202763099934917633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399688555748069866319560709 74941604202763099934917633)
        ·
          refine ⟨56206203152072324951188225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74941604202763099934917633 56206203152072324951188225)
          ·
            refine ⟨42154652364054243713391169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56206203152072324951188225 42154652364054243713391169)
            ·
              refine ⟨31615989273040682785043377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42154652364054243713391169 31615989273040682785043377)
              ·
                refine ⟨23711991954780512088782533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31615989273040682785043377 23711991954780512088782533)
                ·
                  refine ⟨4445998491521346016646725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23711991954780512088782533 4445998491521346016646725)
                  ·
                    refine ⟨833624717160252378121261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4445998491521346016646725 833624717160252378121261)
                    ·
                      rfl

theorem cell23_4870435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 4, 4].length) (baseStart_4870435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870435 prefixEnd_4870435 := by exact prefixLift 4870435
  have htrace : WordTrace (prefixWord ++ tailWord_4870435) baseStart_4870435 baseEnd_4870435 := by
    simpa [prefixWord, tailWord_4870435, baseEnd_4870435] using wordTrace_append hprefix tailTrace_4870435
  have hstable : (prefixWord ++ tailWord_4870435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870435).length < 2 ^ (prefixWord ++ tailWord_4870435).sum := by decide
  have hdescent : baseEnd_4870435 < baseStart_4870435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870436 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_4870436 : Nat := 118140960795 + 4870436 * 2 ^ 59
def prefixEnd_4870436 : Nat := 4983230072969 + 3 ^ 40 * 4870436 * 2
def baseEnd_4870436 : Nat := 2500874664961411630451279

theorem tailTrace_4870436 : CollatzResearch.WordTrace tailWord_4870436 prefixEnd_4870436 2500874664961411630451279 := by
  unfold tailWord_4870436
  simp only [CollatzResearch.WordTrace]
  refine ⟨88819697291624825545295581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118426263055499767393727441 88819697291624825545295581)
  ·
    refine ⟨33307386484359309579485843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88819697291624825545295581 33307386484359309579485843)
    ·
      refine ⟨49961079726538964369228765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33307386484359309579485843 49961079726538964369228765)
      ·
        refine ⟨18735404897452111638460787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49961079726538964369228765 18735404897452111638460787)
        ·
          refine ⟨28103107346178167457691181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18735404897452111638460787 28103107346178167457691181)
          ·
            refine ⟨10538665254816812796634193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28103107346178167457691181 10538665254816812796634193)
            ·
              refine ⟨7903998941112609597475645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10538665254816812796634193 7903998941112609597475645)
              ·
                refine ⟨2963999602917228599053367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7903998941112609597475645 2963999602917228599053367)
                ·
                  refine ⟨4445999404375842898580051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2963999602917228599053367 4445999404375842898580051)
                  ·
                    refine ⟨6668999106563764347870077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4445999404375842898580051 6668999106563764347870077)
                    ·
                      refine ⟨2500874664961411630451279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6668999106563764347870077 2500874664961411630451279)
                      ·
                        rfl

theorem cell23_4870436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_4870436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870436 prefixEnd_4870436 := by exact prefixLift 4870436
  have htrace : WordTrace (prefixWord ++ tailWord_4870436) baseStart_4870436 baseEnd_4870436 := by
    simpa [prefixWord, tailWord_4870436, baseEnd_4870436] using wordTrace_append hprefix tailTrace_4870436
  have hstable : (prefixWord ++ tailWord_4870436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870436).length < 2 ^ (prefixWord ++ tailWord_4870436).sum := by decide
  have hdescent : baseEnd_4870436 < baseStart_4870436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870462 : List Nat := [4, 2, 1, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_4870462 : Nat := 118140960795 + 4870462 * 2 ^ 59
def prefixEnd_4870462 : Nat := 4983230072969 + 3 ^ 40 * 4870462 * 2
def baseEnd_4870462 : Nat := 2500888015458428528726159

theorem tailTrace_4870462 : CollatzResearch.WordTrace tailWord_4870462 prefixEnd_4870462 2500888015458428528726159 := by
  unfold tailWord_4870462
  simp only [CollatzResearch.WordTrace]
  refine ⟨22205042860144432191379705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118426895254103638354025093 22205042860144432191379705)
  ·
    refine ⟨16653782145108324143534779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22205042860144432191379705 16653782145108324143534779)
    ·
      refine ⟨24980673217662486215302169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16653782145108324143534779 24980673217662486215302169)
      ·
        refine ⟨18735504913246864661476627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24980673217662486215302169 18735504913246864661476627)
        ·
          refine ⟨28103257369870296992214941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18735504913246864661476627 28103257369870296992214941)
          ·
            refine ⟨10538721513701361372080603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28103257369870296992214941 10538721513701361372080603)
            ·
              refine ⟨15808082270552042058120905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10538721513701361372080603 15808082270552042058120905)
              ·
                refine ⟨11856061702914031543590679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15808082270552042058120905 11856061702914031543590679)
                ·
                  refine ⟨17784092554371047315386019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11856061702914031543590679 17784092554371047315386019)
                  ·
                    refine ⟨26676138831556570973079029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17784092554371047315386019 26676138831556570973079029)
                    ·
                      refine ⟨2500888015458428528726159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26676138831556570973079029 2500888015458428528726159)
                      ·
                        rfl

theorem cell23_4870462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_4870462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870462 prefixEnd_4870462 := by exact prefixLift 4870462
  have htrace : WordTrace (prefixWord ++ tailWord_4870462) baseStart_4870462 baseEnd_4870462 := by
    simpa [prefixWord, tailWord_4870462, baseEnd_4870462] using wordTrace_append hprefix tailTrace_4870462
  have hstable : (prefixWord ++ tailWord_4870462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870462).length < 2 ^ (prefixWord ++ tailWord_4870462).sum := by decide
  have hdescent : baseEnd_4870462 < baseStart_4870462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870475 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3]
def baseStart_4870475 : Nat := 118140960795 + 4870475 * 2 ^ 59
def prefixEnd_4870475 : Nat := 4983230072969 + 3 ^ 40 * 4870475 * 2
def baseEnd_4870475 : Nat := 2500894690706936977863599

theorem tailTrace_4870475 : CollatzResearch.WordTrace tailWord_4870475 prefixEnd_4870475 2500894690706936977863599 := by
  unfold tailWord_4870475
  simp only [CollatzResearch.WordTrace]
  refine ⟨177640817030108360751260879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118427211353405573834173919 177640817030108360751260879)
  ·
    refine ⟨266461225545162541126891319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177640817030108360751260879 266461225545162541126891319)
    ·
      refine ⟨399691838317743811690336979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266461225545162541126891319 399691838317743811690336979)
      ·
        refine ⟨599537757476615717535505469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399691838317743811690336979 599537757476615717535505469)
        ·
          refine ⟨224826659053730894075814551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 599537757476615717535505469 224826659053730894075814551)
          ·
            refine ⟨337239988580596341113721827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224826659053730894075814551 337239988580596341113721827)
            ·
              refine ⟨505859982870894511670582741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337239988580596341113721827 505859982870894511670582741)
              ·
                refine ⟨11856093348536590117279283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 505859982870894511670582741 11856093348536590117279283)
                ·
                  refine ⟨17784140022804885175918925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11856093348536590117279283 17784140022804885175918925)
                  ·
                    refine ⟨6669052508551831940969597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17784140022804885175918925 6669052508551831940969597)
                    ·
                      refine ⟨2500894690706936977863599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669052508551831940969597 2500894690706936977863599)
                      ·
                        rfl

theorem cell23_4870475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 3, 3].length) (baseStart_4870475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870475 prefixEnd_4870475 := by exact prefixLift 4870475
  have htrace : WordTrace (prefixWord ++ tailWord_4870475) baseStart_4870475 baseEnd_4870475 := by
    simpa [prefixWord, tailWord_4870475, baseEnd_4870475] using wordTrace_append hprefix tailTrace_4870475
  have hstable : (prefixWord ++ tailWord_4870475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870475).length < 2 ^ (prefixWord ++ tailWord_4870475).sum := by decide
  have hdescent : baseEnd_4870475 < baseStart_4870475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870509 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_4870509 : Nat := 118140960795 + 4870509 * 2 ^ 59
def prefixEnd_4870509 : Nat := 4983230072969 + 3 ^ 40 * 4870509 * 2
def baseEnd_4870509 : Nat := 2500912149049189844838443

theorem tailTrace_4870509 : CollatzResearch.WordTrace tailWord_4870509 prefixEnd_4870509 2500912149049189844838443 := by
  unfold tailWord_4870509
  simp only [CollatzResearch.WordTrace]
  refine ⟨177642057111985184557998581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118428038074656789705332387 177642057111985184557998581)
  ·
    refine ⟨16653942854248611052312367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177642057111985184557998581 16653942854248611052312367)
    ·
      refine ⟨24980914281372916578468551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16653942854248611052312367 24980914281372916578468551)
      ·
        refine ⟨37471371422059374867702827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24980914281372916578468551 37471371422059374867702827)
        ·
          refine ⟨56207057133089062301554241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37471371422059374867702827 56207057133089062301554241)
          ·
            refine ⟨42155292849816796726165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56207057133089062301554241 42155292849816796726165681)
            ·
              refine ⟨31616469637362597544624261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42155292849816796726165681 31616469637362597544624261)
              ·
                refine ⟨5928088057005487039617049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31616469637362597544624261 5928088057005487039617049)
                ·
                  refine ⟨4446066042754115279712787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928088057005487039617049 4446066042754115279712787)
                  ·
                    refine ⟨6669099064131172919569181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4446066042754115279712787 6669099064131172919569181)
                    ·
                      refine ⟨2500912149049189844838443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669099064131172919569181 2500912149049189844838443)
                      ·
                        rfl

theorem cell23_4870509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_4870509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870509 prefixEnd_4870509 := by exact prefixLift 4870509
  have htrace : WordTrace (prefixWord ++ tailWord_4870509) baseStart_4870509 baseEnd_4870509 := by
    simpa [prefixWord, tailWord_4870509, baseEnd_4870509] using wordTrace_append hprefix tailTrace_4870509
  have hstable : (prefixWord ++ tailWord_4870509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870509).length < 2 ^ (prefixWord ++ tailWord_4870509).sum := by decide
  have hdescent : baseEnd_4870509 < baseStart_4870509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870530 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_4870530 : Nat := 118140960795 + 4870530 * 2 ^ 59
def prefixEnd_4870530 : Nat := 4983230072969 + 3 ^ 40 * 4870530 * 2
def baseEnd_4870530 : Nat := 2500922932142934262675847

theorem tailTrace_4870530 : CollatzResearch.WordTrace tailWord_4870530 prefixEnd_4870530 2500922932142934262675847 := by
  unfold tailWord_4870530
  simp only [CollatzResearch.WordTrace]
  refine ⟨44410705761227276286128261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118428548696606070096342029 44410705761227276286128261)
  ·
    refine ⟨8327007330230114303649049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44410705761227276286128261 8327007330230114303649049)
    ·
      refine ⟨6245255497672585727736787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8327007330230114303649049 6245255497672585727736787)
      ·
        refine ⟨9367883246508878591605181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245255497672585727736787 9367883246508878591605181)
        ·
          refine ⟨3512956217440829471851943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9367883246508878591605181 3512956217440829471851943)
          ·
            refine ⟨5269434326161244207777915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512956217440829471851943 5269434326161244207777915)
            ·
              refine ⟨7904151489241866311666873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269434326161244207777915 7904151489241866311666873)
              ·
                refine ⟨5928113616931399733750155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7904151489241866311666873 5928113616931399733750155)
                ·
                  refine ⟨8892170425397099600625233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5928113616931399733750155 8892170425397099600625233)
                  ·
                    refine ⟨6669127819047824700468925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8892170425397099600625233 6669127819047824700468925)
                    ·
                      refine ⟨2500922932142934262675847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669127819047824700468925 2500922932142934262675847)
                      ·
                        rfl

theorem cell23_4870530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_4870530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870530 prefixEnd_4870530 := by exact prefixLift 4870530
  have htrace : WordTrace (prefixWord ++ tailWord_4870530) baseStart_4870530 baseEnd_4870530 := by
    simpa [prefixWord, tailWord_4870530, baseEnd_4870530] using wordTrace_append hprefix tailTrace_4870530
  have hstable : (prefixWord ++ tailWord_4870530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870530).length < 2 ^ (prefixWord ++ tailWord_4870530).sum := by decide
  have hdescent : baseEnd_4870530 < baseStart_4870530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870535 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_4870535 : Nat := 118140960795 + 4870535 * 2 ^ 59
def prefixEnd_4870535 : Nat := 4983230072969 + 3 ^ 40 * 4870535 * 2
def baseEnd_4870535 : Nat := 2500925499546206743113323

theorem tailTrace_4870535 : CollatzResearch.WordTrace tailWord_4870535 prefixEnd_4870535 2500925499546206743113323 := by
  unfold tailWord_4870535
  simp only [CollatzResearch.WordTrace]
  refine ⟨177643005409890990998445059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118428670273260660665630039 177643005409890990998445059)
  ·
    refine ⟨266464508114836486497667589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177643005409890990998445059 266464508114836486497667589)
    ·
      refine ⟨49962095271531841218312673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266464508114836486497667589 49962095271531841218312673)
      ·
        refine ⟨37471571453648880913734505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49962095271531841218312673 37471571453648880913734505)
        ·
          refine ⟨28103678590236660685300879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37471571453648880913734505 28103678590236660685300879)
          ·
            refine ⟨42155517885354991027951319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28103678590236660685300879 42155517885354991027951319)
            ·
              refine ⟨63233276828032486541926979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42155517885354991027951319 63233276828032486541926979)
              ·
                refine ⟨94849915242048729812890469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63233276828032486541926979 94849915242048729812890469)
                ·
                  refine ⟨17784359107884136839916963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94849915242048729812890469 17784359107884136839916963)
                  ·
                    refine ⟨26676538661826205259875445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17784359107884136839916963 26676538661826205259875445)
                    ·
                      refine ⟨2500925499546206743113323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26676538661826205259875445 2500925499546206743113323)
                      ·
                        rfl

theorem cell23_4870535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_4870535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870535 prefixEnd_4870535 := by exact prefixLift 4870535
  have htrace : WordTrace (prefixWord ++ tailWord_4870535) baseStart_4870535 baseEnd_4870535 := by
    simpa [prefixWord, tailWord_4870535, baseEnd_4870535] using wordTrace_append hprefix tailTrace_4870535
  have hstable : (prefixWord ++ tailWord_4870535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870535).length < 2 ^ (prefixWord ++ tailWord_4870535).sum := by decide
  have hdescent : baseEnd_4870535 < baseStart_4870535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870552 : List Nat := [2, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5]
def baseStart_4870552 : Nat := 118140960795 + 4870552 * 2 ^ 59
def prefixEnd_4870552 : Nat := 4983230072969 + 3 ^ 40 * 4870552 * 2
def baseEnd_4870552 : Nat := 2500934228717333176600745

theorem tailTrace_4870552 : CollatzResearch.WordTrace tailWord_4870552 prefixEnd_4870552 2500934228717333176600745 := by
  unfold tailWord_4870552
  simp only [CollatzResearch.WordTrace]
  refine ⟨88821812725414701450906955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118429083633886268601209273 88821812725414701450906955)
  ·
    refine ⟨133232719088122052176360433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88821812725414701450906955 133232719088122052176360433)
    ·
      refine ⟨99924539316091539132270325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133232719088122052176360433 99924539316091539132270325)
      ·
        refine ⟨9367925560883581793650343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99924539316091539132270325 9367925560883581793650343)
        ·
          refine ⟨14051888341325372690475515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9367925560883581793650343 14051888341325372690475515)
          ·
            refine ⟨21077832511988059035713273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14051888341325372690475515 21077832511988059035713273)
            ·
              refine ⟨15808374383991044276784955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21077832511988059035713273 15808374383991044276784955)
              ·
                refine ⟨23712561575986566415177433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15808374383991044276784955 23712561575986566415177433)
                ·
                  refine ⟨17784421181989924811383075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23712561575986566415177433 17784421181989924811383075)
                  ·
                    refine ⟨26676631772984887217074613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17784421181989924811383075 26676631772984887217074613)
                    ·
                      refine ⟨2500934228717333176600745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26676631772984887217074613 2500934228717333176600745)
                      ·
                        rfl

theorem cell23_4870552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_4870552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870552 prefixEnd_4870552 := by exact prefixLift 4870552
  have htrace : WordTrace (prefixWord ++ tailWord_4870552) baseStart_4870552 baseEnd_4870552 := by
    simpa [prefixWord, tailWord_4870552, baseEnd_4870552] using wordTrace_append hprefix tailTrace_4870552
  have hstable : (prefixWord ++ tailWord_4870552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870552).length < 2 ^ (prefixWord ++ tailWord_4870552).sum := by decide
  have hdescent : baseEnd_4870552 < baseStart_4870552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870562 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4870562 : Nat := 118140960795 + 4870562 * 2 ^ 59
def prefixEnd_4870562 : Nat := 4983230072969 + 3 ^ 40 * 4870562 * 2
def baseEnd_4870562 : Nat := 2500939363523878137475699

theorem tailTrace_4870562 : CollatzResearch.WordTrace tailWord_4870562 prefixEnd_4870562 2500939363523878137475699 := by
  unfold tailWord_4870562
  simp only [CollatzResearch.WordTrace]
  refine ⟨44410997545198293652419485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118429326787195449739785293 44410997545198293652419485)
  ·
    refine ⟨16654124079449360119657307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44410997545198293652419485 16654124079449360119657307)
    ·
      refine ⟨24981186119174040179485961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654124079449360119657307 24981186119174040179485961)
      ·
        refine ⟨18735889589380530134614471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24981186119174040179485961 18735889589380530134614471)
        ·
          refine ⟨28103834384070795201921707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18735889589380530134614471 28103834384070795201921707)
          ·
            refine ⟨42155751576106192802882561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28103834384070795201921707 42155751576106192802882561)
            ·
              refine ⟨31616813682079644602161921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42155751576106192802882561 31616813682079644602161921)
              ·
                refine ⟨23712610261559733451621441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31616813682079644602161921 23712610261559733451621441)
                ·
                  refine ⟨17784457696169800088716081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23712610261559733451621441 17784457696169800088716081)
                  ·
                    refine ⟨13338343272127350066537061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17784457696169800088716081 13338343272127350066537061)
                    ·
                      refine ⟨2500939363523878137475699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13338343272127350066537061 2500939363523878137475699)
                      ·
                        rfl

theorem cell23_4870562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4870562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870562 prefixEnd_4870562 := by exact prefixLift 4870562
  have htrace : WordTrace (prefixWord ++ tailWord_4870562) baseStart_4870562 baseEnd_4870562 := by
    simpa [prefixWord, tailWord_4870562, baseEnd_4870562] using wordTrace_append hprefix tailTrace_4870562
  have hstable : (prefixWord ++ tailWord_4870562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870562).length < 2 ^ (prefixWord ++ tailWord_4870562).sum := by decide
  have hdescent : baseEnd_4870562 < baseStart_4870562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870592 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2]
def baseStart_4870592 : Nat := 118140960795 + 4870592 * 2 ^ 59
def prefixEnd_4870592 : Nat := 4983230072969 + 3 ^ 40 * 4870592 * 2
def baseEnd_4870592 : Nat := 2500954767943513020100561

theorem tailTrace_4870592 : CollatzResearch.WordTrace tailWord_4870592 prefixEnd_4870592 2500954767943513020100561 := by
  unfold tailWord_4870592
  simp only [CollatzResearch.WordTrace]
  refine ⟨88822542185342244866635015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118430056247122993155513353 88822542185342244866635015)
  ·
    refine ⟨133233813278013367299952523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88822542185342244866635015 133233813278013367299952523)
    ·
      refine ⟨199850719917020050949928785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133233813278013367299952523 199850719917020050949928785)
      ·
        refine ⟨149888039937765038212446589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199850719917020050949928785 149888039937765038212446589)
        ·
          refine ⟨56208014976661889329667471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149888039937765038212446589 56208014976661889329667471)
          ·
            refine ⟨84312022464992833994501207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56208014976661889329667471 84312022464992833994501207)
            ·
              refine ⟨126468033697489250991751811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84312022464992833994501207 126468033697489250991751811)
              ·
                refine ⟨189702050546233876487627717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126468033697489250991751811 189702050546233876487627717)
                ·
                  refine ⟨35569134477418851841430197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189702050546233876487627717 35569134477418851841430197)
                  ·
                    refine ⟨3334606357258017360134081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35569134477418851841430197 3334606357258017360134081)
                    ·
                      refine ⟨2500954767943513020100561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334606357258017360134081 2500954767943513020100561)
                      ·
                        rfl

theorem cell23_4870592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 4, 5, 2].length) (baseStart_4870592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870592 prefixEnd_4870592 := by exact prefixLift 4870592
  have htrace : WordTrace (prefixWord ++ tailWord_4870592) baseStart_4870592 baseEnd_4870592 := by
    simpa [prefixWord, tailWord_4870592, baseEnd_4870592] using wordTrace_append hprefix tailTrace_4870592
  have hstable : (prefixWord ++ tailWord_4870592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870592).length < 2 ^ (prefixWord ++ tailWord_4870592).sum := by decide
  have hdescent : baseEnd_4870592 < baseStart_4870592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870635 : List Nat := [1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6]
def baseStart_4870635 : Nat := 118140960795 + 4870635 * 2 ^ 59
def prefixEnd_4870635 : Nat := 4983230072969 + 3 ^ 40 * 4870635 * 2
def baseEnd_4870635 : Nat := 2500976847611656351862863

theorem tailTrace_4870635 : CollatzResearch.WordTrace tailWord_4870635 prefixEnd_4870635 2500976847611656351862863 := by
  unfold tailWord_4870635
  simp only [CollatzResearch.WordTrace]
  refine ⟨177646652709528708077085359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118431101806352472051390239 177646652709528708077085359)
  ·
    refine ⟨266469979064293062115628039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177646652709528708077085359 266469979064293062115628039)
    ·
      refine ⟨399704968596439593173442059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266469979064293062115628039 399704968596439593173442059)
      ·
        refine ⟨599557452894659389760163089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399704968596439593173442059 599557452894659389760163089)
        ·
          refine ⟨449668089670994542320122317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599557452894659389760163089 449668089670994542320122317)
          ·
            refine ⟨168625533626622953370045869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449668089670994542320122317 168625533626622953370045869)
            ·
              refine ⟨63234575109983607513767201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168625533626622953370045869 63234575109983607513767201)
              ·
                refine ⟨47425931332487705635325401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63234575109983607513767201 47425931332487705635325401)
                ·
                  refine ⟨35569448499365779226494051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47425931332487705635325401 35569448499365779226494051)
                  ·
                    refine ⟨53354172749048668839741077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35569448499365779226494051 53354172749048668839741077)
                    ·
                      refine ⟨2500976847611656351862863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53354172749048668839741077 2500976847611656351862863)
                      ·
                        rfl

theorem cell23_4870635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 6].length) (baseStart_4870635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870635 prefixEnd_4870635 := by exact prefixLift 4870635
  have htrace : WordTrace (prefixWord ++ tailWord_4870635) baseStart_4870635 baseEnd_4870635 := by
    simpa [prefixWord, tailWord_4870635, baseEnd_4870635] using wordTrace_append hprefix tailTrace_4870635
  have hstable : (prefixWord ++ tailWord_4870635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870635).length < 2 ^ (prefixWord ++ tailWord_4870635).sum := by decide
  have hdescent : baseEnd_4870635 < baseStart_4870635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870665 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 8]
def baseStart_4870665 : Nat := 118140960795 + 4870665 * 2 ^ 59
def prefixEnd_4870665 : Nat := 4983230072969 + 3 ^ 40 * 4870665 * 2
def baseEnd_4870665 : Nat := 2500992252031291234487725

theorem tailTrace_4870665 : CollatzResearch.WordTrace tailWord_4870665 prefixEnd_4870665 2500992252031291234487725 := by
  unfold tailWord_4870665
  simp only [CollatzResearch.WordTrace]
  refine ⟨177647746899420023200677449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118431831266280015467118299 177647746899420023200677449)
  ·
    refine ⟨133235810174565017400508087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177647746899420023200677449 133235810174565017400508087)
    ·
      refine ⟨199853715261847526100762131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133235810174565017400508087 199853715261847526100762131)
      ·
        refine ⟨299780572892771289151143197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199853715261847526100762131 299780572892771289151143197)
        ·
          refine ⟨112417714834789233431678699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299780572892771289151143197 112417714834789233431678699)
          ·
            refine ⟨168626572252183850147518049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112417714834789233431678699 168626572252183850147518049)
            ·
              refine ⟨126469929189137887610638537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168626572252183850147518049 126469929189137887610638537)
              ·
                refine ⟨94852446891853415707978903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126469929189137887610638537 94852446891853415707978903)
                ·
                  refine ⟨142278670337780123561968355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94852446891853415707978903 142278670337780123561968355)
                  ·
                    refine ⟨213418005506670185342952533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142278670337780123561968355 213418005506670185342952533)
                    ·
                      refine ⟨2500992252031291234487725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213418005506670185342952533 2500992252031291234487725)
                      ·
                        rfl

theorem cell23_4870665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 1, 8].length) (baseStart_4870665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870665 prefixEnd_4870665 := by exact prefixLift 4870665
  have htrace : WordTrace (prefixWord ++ tailWord_4870665) baseStart_4870665 baseEnd_4870665 := by
    simpa [prefixWord, tailWord_4870665, baseEnd_4870665] using wordTrace_append hprefix tailTrace_4870665
  have hstable : (prefixWord ++ tailWord_4870665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870665).length < 2 ^ (prefixWord ++ tailWord_4870665).sum := by decide
  have hdescent : baseEnd_4870665 < baseStart_4870665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870676 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_4870676 : Nat := 118140960795 + 4870676 * 2 ^ 59
def prefixEnd_4870676 : Nat := 4983230072969 + 3 ^ 40 * 4870676 * 2
def baseEnd_4870676 : Nat := 2500997900318490691450175

theorem tailTrace_4870676 : CollatzResearch.WordTrace tailWord_4870676 prefixEnd_4870676 2500997900318490691450175 := by
  unfold tailWord_4870676
  simp only [CollatzResearch.WordTrace]
  refine ⟨88824074051190086039663941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118432098734920114719551921 88824074051190086039663941)
  ·
    refine ⟨16654513884598141132436989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88824074051190086039663941 16654513884598141132436989)
    ·
      refine ⟨6245442706724302924663871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16654513884598141132436989 6245442706724302924663871)
      ·
        refine ⟨9368164060086454386995807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6245442706724302924663871 9368164060086454386995807)
        ·
          refine ⟨14052246090129681580493711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368164060086454386995807 14052246090129681580493711)
          ·
            refine ⟨21078369135194522370740567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052246090129681580493711 21078369135194522370740567)
            ·
              refine ⟨31617553702791783556110851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21078369135194522370740567 31617553702791783556110851)
              ·
                refine ⟨47426330554187675334166277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31617553702791783556110851 47426330554187675334166277)
                ·
                  refine ⟨8892436978910189125156177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47426330554187675334166277 8892436978910189125156177)
                  ·
                    refine ⟨6669327734182641843867133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8892436978910189125156177 6669327734182641843867133)
                    ·
                      refine ⟨2500997900318490691450175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669327734182641843867133 2500997900318490691450175)
                      ·
                        rfl

theorem cell23_4870676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_4870676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870676 prefixEnd_4870676 := by exact prefixLift 4870676
  have htrace : WordTrace (prefixWord ++ tailWord_4870676) baseStart_4870676 baseEnd_4870676 := by
    simpa [prefixWord, tailWord_4870676, baseEnd_4870676] using wordTrace_append hprefix tailTrace_4870676
  have hstable : (prefixWord ++ tailWord_4870676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870676).length < 2 ^ (prefixWord ++ tailWord_4870676).sum := by decide
  have hdescent : baseEnd_4870676 < baseStart_4870676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870696 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 6]
def baseStart_4870696 : Nat := 118140960795 + 4870696 * 2 ^ 59
def prefixEnd_4870696 : Nat := 4983230072969 + 3 ^ 40 * 4870696 * 2
def baseEnd_4870696 : Nat := 277889796659064512577787

theorem tailTrace_4870696 : CollatzResearch.WordTrace tailWord_4870696 prefixEnd_4870696 277889796659064512577787 := by
  unfold tailWord_4870696
  simp only [CollatzResearch.WordTrace]
  refine ⟨88824438781153857747527971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118432585041538476996703961 88824438781153857747527971)
  ·
    refine ⟨133236658171730786621291957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88824438781153857747527971 133236658171730786621291957)
    ·
      refine ⟨12490936703599761245746121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133236658171730786621291957 12490936703599761245746121)
      ·
        refine ⟨9368202527699820934309591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12490936703599761245746121 9368202527699820934309591)
        ·
          refine ⟨14052303791549731401464387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368202527699820934309591 14052303791549731401464387)
          ·
            refine ⟨21078455687324597102196581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052303791549731401464387 21078455687324597102196581)
            ·
              refine ⟨3952210441373361956661859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21078455687324597102196581 3952210441373361956661859)
              ·
                refine ⟨5928315662060042934992789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952210441373361956661859 5928315662060042934992789)
                ·
                  refine ⟨277889796659064512577787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5928315662060042934992789 277889796659064512577787)
                  ·
                    rfl

theorem cell23_4870696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 6].length) (baseStart_4870696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870696 prefixEnd_4870696 := by exact prefixLift 4870696
  have htrace : WordTrace (prefixWord ++ tailWord_4870696) baseStart_4870696 baseEnd_4870696 := by
    simpa [prefixWord, tailWord_4870696, baseEnd_4870696] using wordTrace_append hprefix tailTrace_4870696
  have hstable : (prefixWord ++ tailWord_4870696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870696).length < 2 ^ (prefixWord ++ tailWord_4870696).sum := by decide
  have hdescent : baseEnd_4870696 < baseStart_4870696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870716 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_4870716 : Nat := 118140960795 + 4870716 * 2 ^ 59
def prefixEnd_4870716 : Nat := 4983230072969 + 3 ^ 40 * 4870716 * 2
def baseEnd_4870716 : Nat := 2501018439544670534949991

theorem tailTrace_4870716 : CollatzResearch.WordTrace tailWord_4870716 prefixEnd_4870716 2501018439544670534949991 := by
  unfold tailWord_4870716
  simp only [CollatzResearch.WordTrace]
  refine ⟨88824803511117629455392001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118433071348156839273856001 88824803511117629455392001)
  ·
    refine ⟨66618602633338222091544001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88824803511117629455392001 66618602633338222091544001)
    ·
      refine ⟨49963951975003666568658001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66618602633338222091544001 49963951975003666568658001)
      ·
        refine ⟨37472963981252749926493501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49963951975003666568658001 37472963981252749926493501)
        ·
          refine ⟨14052361492969781222435063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37472963981252749926493501 14052361492969781222435063)
          ·
            refine ⟨21078542239454671833652595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052361492969781222435063 21078542239454671833652595)
            ·
              refine ⟨31617813359182007750478893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21078542239454671833652595 31617813359182007750478893)
              ·
                refine ⟨11856680009693252906429585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31617813359182007750478893 11856680009693252906429585)
                ·
                  refine ⟨8892510007269939679822189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11856680009693252906429585 8892510007269939679822189)
                  ·
                    refine ⟨3334691252726227379933321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8892510007269939679822189 3334691252726227379933321)
                    ·
                      refine ⟨2501018439544670534949991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334691252726227379933321 2501018439544670534949991)
                      ·
                        rfl

theorem cell23_4870716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_4870716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870716 prefixEnd_4870716 := by exact prefixLift 4870716
  have htrace : WordTrace (prefixWord ++ tailWord_4870716) baseStart_4870716 baseEnd_4870716 := by
    simpa [prefixWord, tailWord_4870716, baseEnd_4870716] using wordTrace_append hprefix tailTrace_4870716
  have hstable : (prefixWord ++ tailWord_4870716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870716).length < 2 ^ (prefixWord ++ tailWord_4870716).sum := by decide
  have hdescent : baseEnd_4870716 < baseStart_4870716 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870733 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 2, 3, 2]
def baseStart_4870733 : Nat := 118140960795 + 4870733 * 2 ^ 59
def prefixEnd_4870733 : Nat := 4983230072969 + 3 ^ 40 * 4870733 * 2
def baseEnd_4870733 : Nat := 2501027168715796968437413

theorem tailTrace_4870733 : CollatzResearch.WordTrace tailWord_4870733 prefixEnd_4870733 2501027168715796968437413 := by
  unfold tailWord_4870733
  simp only [CollatzResearch.WordTrace]
  refine ⟨177650227063173670814152853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118433484708782447209435235 177650227063173670814152853)
  ·
    refine ⟨8327354393586265819413415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177650227063173670814152853 8327354393586265819413415)
    ·
      refine ⟨12491031590379398729120123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8327354393586265819413415 12491031590379398729120123)
      ·
        refine ⟨18736547385569098093680185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12491031590379398729120123 18736547385569098093680185)
        ·
          refine ⟨14052410539176823570260139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18736547385569098093680185 14052410539176823570260139)
          ·
            refine ⟨21078615808765235355390209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052410539176823570260139 21078615808765235355390209)
            ·
              refine ⟨15808961856573926516542657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21078615808765235355390209 15808961856573926516542657)
              ·
                refine ⟨11856721392430444887406993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15808961856573926516542657 11856721392430444887406993)
                ·
                  refine ⟨8892541044322833665555245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11856721392430444887406993 8892541044322833665555245)
                  ·
                    refine ⟨3334702891621062624583217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8892541044322833665555245 3334702891621062624583217)
                    ·
                      refine ⟨2501027168715796968437413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3334702891621062624583217 2501027168715796968437413)
                      ·
                        rfl

theorem cell23_4870733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_4870733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870733 prefixEnd_4870733 := by exact prefixLift 4870733
  have htrace : WordTrace (prefixWord ++ tailWord_4870733) baseStart_4870733 baseEnd_4870733 := by
    simpa [prefixWord, tailWord_4870733, baseEnd_4870733] using wordTrace_append hprefix tailTrace_4870733
  have hstable : (prefixWord ++ tailWord_4870733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870733).length < 2 ^ (prefixWord ++ tailWord_4870733).sum := by decide
  have hdescent : baseEnd_4870733 < baseStart_4870733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870740 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_4870740 : Nat := 118140960795 + 4870740 * 2 ^ 59
def prefixEnd_4870740 : Nat := 4983230072969 + 3 ^ 40 * 4870740 * 2
def baseEnd_4870740 : Nat := 2501030763080378441049881

theorem tailTrace_4870740 : CollatzResearch.WordTrace tailWord_4870740 prefixEnd_4870740 2501030763080378441049881 := by
  unfold tailWord_4870740
  simp only [CollatzResearch.WordTrace]
  refine ⟨88825241187074155504828837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118433654916098874006438449 88825241187074155504828837)
  ·
    refine ⟨16654732722576404157155407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88825241187074155504828837 16654732722576404157155407)
    ·
      refine ⟨24982099083864606235733111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16654732722576404157155407 24982099083864606235733111)
      ·
        refine ⟨37473148625796909353599667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24982099083864606235733111 37473148625796909353599667)
        ·
          refine ⟨56209722938695364030399501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37473148625796909353599667 56209722938695364030399501)
          ·
            refine ⟨21078646102010761511399813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56209722938695364030399501 21078646102010761511399813)
            ·
              refine ⟨3952246144127017783387465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21078646102010761511399813 3952246144127017783387465)
              ·
                refine ⟨2964184608095263337540599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3952246144127017783387465 2964184608095263337540599)
                ·
                  refine ⟨4446276912142895006310899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964184608095263337540599 4446276912142895006310899)
                  ·
                    refine ⟨6669415368214342509466349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4446276912142895006310899 6669415368214342509466349)
                    ·
                      refine ⟨2501030763080378441049881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669415368214342509466349 2501030763080378441049881)
                      ·
                        rfl

theorem cell23_4870740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_4870740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870740 prefixEnd_4870740 := by exact prefixLift 4870740
  have htrace : WordTrace (prefixWord ++ tailWord_4870740) baseStart_4870740 baseEnd_4870740 := by
    simpa [prefixWord, tailWord_4870740, baseEnd_4870740] using wordTrace_append hprefix tailTrace_4870740
  have hstable : (prefixWord ++ tailWord_4870740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870740).length < 2 ^ (prefixWord ++ tailWord_4870740).sum := by decide
  have hdescent : baseEnd_4870740 < baseStart_4870740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870752 : List Nat := [2, 1, 1, 3, 2, 1, 5, 8]
def baseStart_4870752 : Nat := 118140960795 + 4870752 * 2 ^ 59
def prefixEnd_4870752 : Nat := 4983230072969 + 3 ^ 40 * 4870752 * 2
def baseEnd_4870752 : Nat := 92630997216601199781475

theorem tailTrace_4870752 : CollatzResearch.WordTrace tailWord_4870752 prefixEnd_4870752 92630997216601199781475 := by
  unfold tailWord_4870752
  simp only [CollatzResearch.WordTrace]
  refine ⟨88825460025052418529547255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118433946700069891372729673 88825460025052418529547255)
  ·
    refine ⟨133238190037578627794320883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88825460025052418529547255 133238190037578627794320883)
    ·
      refine ⟨199857285056367941691481325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133238190037578627794320883 199857285056367941691481325)
      ·
        refine ⟨74946481896137978134305497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199857285056367941691481325 74946481896137978134305497)
        ·
          refine ⟨56209861422103483600729123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74946481896137978134305497 56209861422103483600729123)
          ·
            refine ⟨84314792133155225401093685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56209861422103483600729123 84314792133155225401093685)
            ·
              refine ⟨7904511762483302381352533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84314792133155225401093685 7904511762483302381352533)
              ·
                refine ⟨92630997216601199781475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7904511762483302381352533 92630997216601199781475)
                ·
                  rfl

theorem cell23_4870752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 5, 8].length) (baseStart_4870752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870752 prefixEnd_4870752 := by exact prefixLift 4870752
  have htrace : WordTrace (prefixWord ++ tailWord_4870752) baseStart_4870752 baseEnd_4870752 := by
    simpa [prefixWord, tailWord_4870752, baseEnd_4870752] using wordTrace_append hprefix tailTrace_4870752
  have hstable : (prefixWord ++ tailWord_4870752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870752).length < 2 ^ (prefixWord ++ tailWord_4870752).sum := by decide
  have hdescent : baseEnd_4870752 < baseStart_4870752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870766 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3]
def baseStart_4870766 : Nat := 118140960795 + 4870766 * 2 ^ 59
def prefixEnd_4870766 : Nat := 4983230072969 + 3 ^ 40 * 4870766 * 2
def baseEnd_4870766 : Nat := 2501044113577395339324761

theorem tailTrace_4870766 : CollatzResearch.WordTrace tailWord_4870766 prefixEnd_4870766 2501044113577395339324761 := by
  unfold tailWord_4870766
  simp only [CollatzResearch.WordTrace]
  refine ⟨22206428834006764681263019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118434287114702744966736101 22206428834006764681263019)
  ·
    refine ⟨33309643251010147021894529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22206428834006764681263019 33309643251010147021894529)
    ·
      refine ⟨24982232438257610266420897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33309643251010147021894529 24982232438257610266420897)
      ·
        refine ⟨18736674328693207699815673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24982232438257610266420897 18736674328693207699815673)
        ·
          refine ⟨14052505746519905774861755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18736674328693207699815673 14052505746519905774861755)
          ·
            refine ⟨21078758619779858662292633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052505746519905774861755 21078758619779858662292633)
            ·
              refine ⟨15809068964834893996719475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21078758619779858662292633 15809068964834893996719475)
              ·
                refine ⟨23713603447252340995079213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15809068964834893996719475 23713603447252340995079213)
                ·
                  refine ⟨8892601292719627873154705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23713603447252340995079213 8892601292719627873154705)
                  ·
                    refine ⟨6669450969539720904866029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8892601292719627873154705 6669450969539720904866029)
                    ·
                      refine ⟨2501044113577395339324761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669450969539720904866029 2501044113577395339324761)
                      ·
                        rfl

theorem cell23_4870766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_4870766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870766 prefixEnd_4870766 := by exact prefixLift 4870766
  have htrace : WordTrace (prefixWord ++ tailWord_4870766) baseStart_4870766 baseEnd_4870766 := by
    simpa [prefixWord, tailWord_4870766, baseEnd_4870766] using wordTrace_append hprefix tailTrace_4870766
  have hstable : (prefixWord ++ tailWord_4870766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870766).length < 2 ^ (prefixWord ++ tailWord_4870766).sum := by decide
  have hdescent : baseEnd_4870766 < baseStart_4870766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870796 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_4870796 : Nat := 118140960795 + 4870796 * 2 ^ 59
def prefixEnd_4870796 : Nat := 4983230072969 + 3 ^ 40 * 4870796 * 2
def baseEnd_4870796 : Nat := 2501059517997030221949623

theorem tailTrace_4870796 : CollatzResearch.WordTrace tailWord_4870796 prefixEnd_4870796 2501059517997030221949623 := by
  unfold tailWord_4870796
  simp only [CollatzResearch.WordTrace]
  refine ⟨88826262430972716286848121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118435016574630288382464161 88826262430972716286848121)
  ·
    refine ⟨66619696823229537215136091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88826262430972716286848121 66619696823229537215136091)
    ·
      refine ⟨99929545234844305822704137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66619696823229537215136091 99929545234844305822704137)
      ·
        refine ⟨74947158926133229367028103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99929545234844305822704137 74947158926133229367028103)
        ·
          refine ⟨112420738389199844050542155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74947158926133229367028103 112420738389199844050542155)
          ·
            refine ⟨168631107583799766075813233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112420738389199844050542155 168631107583799766075813233)
            ·
              refine ⟨126473330687849824556859925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168631107583799766075813233 126473330687849824556859925)
              ·
                refine ⟨5928437375992960526102809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126473330687849824556859925 5928437375992960526102809)
                ·
                  refine ⟨4446328031994720394577107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928437375992960526102809 4446328031994720394577107)
                  ·
                    refine ⟨6669492047992080591865661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4446328031994720394577107 6669492047992080591865661)
                    ·
                      refine ⟨2501059517997030221949623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6669492047992080591865661 2501059517997030221949623)
                      ·
                        rfl

theorem cell23_4870796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_4870796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870796 prefixEnd_4870796 := by exact prefixLift 4870796
  have htrace : WordTrace (prefixWord ++ tailWord_4870796) baseStart_4870796 baseEnd_4870796 := by
    simpa [prefixWord, tailWord_4870796, baseEnd_4870796] using wordTrace_append hprefix tailTrace_4870796
  have hstable : (prefixWord ++ tailWord_4870796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870796).length < 2 ^ (prefixWord ++ tailWord_4870796).sum := by decide
  have hdescent : baseEnd_4870796 < baseStart_4870796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870810 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4870810 : Nat := 118140960795 + 4870810 * 2 ^ 59
def prefixEnd_4870810 : Nat := 4983230072969 + 3 ^ 40 * 4870810 * 2
def baseEnd_4870810 : Nat := 2501066706726193167174559

theorem tailTrace_4870810 : CollatzResearch.WordTrace tailWord_4870810 prefixEnd_4870810 2501066706726193167174559 := by
  unfold tailWord_4870810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44413258870973678241176471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118435356989263141976470589 44413258870973678241176471)
  ·
    refine ⟨66619888306460517361764707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44413258870973678241176471 66619888306460517361764707)
    ·
      refine ⟨99929832459690776042647061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66619888306460517361764707 99929832459690776042647061)
      ·
        refine ⟨4684210896548005126999081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99929832459690776042647061 4684210896548005126999081)
        ·
          refine ⟨3513158172411003845249311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4684210896548005126999081 3513158172411003845249311)
          ·
            refine ⟨5269737258616505767873967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513158172411003845249311 5269737258616505767873967)
            ·
              refine ⟨7904605887924758651810951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269737258616505767873967 7904605887924758651810951)
              ·
                refine ⟨11856908831887137977716427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904605887924758651810951 11856908831887137977716427)
                ·
                  refine ⟨17785363247830706966574641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11856908831887137977716427 17785363247830706966574641)
                  ·
                    refine ⟨13339022435873030224930981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17785363247830706966574641 13339022435873030224930981)
                    ·
                      refine ⟨2501066706726193167174559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13339022435873030224930981 2501066706726193167174559)
                      ·
                        rfl

theorem cell23_4870810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4870810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870810 prefixEnd_4870810 := by exact prefixLift 4870810
  have htrace : WordTrace (prefixWord ++ tailWord_4870810) baseStart_4870810 baseEnd_4870810 := by
    simpa [prefixWord, tailWord_4870810, baseEnd_4870810] using wordTrace_append hprefix tailTrace_4870810
  have hstable : (prefixWord ++ tailWord_4870810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870810).length < 2 ^ (prefixWord ++ tailWord_4870810).sum := by decide
  have hdescent : baseEnd_4870810 < baseStart_4870810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870889 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 2, 5]
def baseStart_4870889 : Nat := 118140960795 + 4870889 * 2 ^ 59
def prefixEnd_4870889 : Nat := 4983230072969 + 3 ^ 40 * 4870889 * 2
def baseEnd_4870889 : Nat := 833702423899299452695565

theorem tailTrace_4870889 : CollatzResearch.WordTrace tailWord_4870889 prefixEnd_4870889 833702423899299452695565 := by
  unfold tailWord_4870889
  simp only [CollatzResearch.WordTrace]
  refine ⟨177655916850608509456831721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118437277900405672971221147 177655916850608509456831721)
  ·
    refine ⟨133241937637956382092623791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177655916850608509456831721 133241937637956382092623791)
    ·
      refine ⟨199862906456934573138935687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133241937637956382092623791 199862906456934573138935687)
      ·
        refine ⟨299794359685401859708403531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199862906456934573138935687 299794359685401859708403531)
        ·
          refine ⟨449691539528102789562605297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299794359685401859708403531 449691539528102789562605297)
          ·
            refine ⟨337268654646077092171953973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 449691539528102789562605297 337268654646077092171953973)
            ·
              refine ⟨31618936373069727391120685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337268654646077092171953973 31618936373069727391120685)
              ·
                refine ⟨11857101139901147771670257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31618936373069727391120685 11857101139901147771670257)
                ·
                  refine ⟨8892825854925860828752693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11857101139901147771670257 8892825854925860828752693)
                  ·
                    refine ⟨833702423899299452695565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8892825854925860828752693 833702423899299452695565)
                    ·
                      rfl

theorem cell23_4870889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 5].length) (baseStart_4870889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870889 prefixEnd_4870889 := by exact prefixLift 4870889
  have htrace : WordTrace (prefixWord ++ tailWord_4870889) baseStart_4870889 baseEnd_4870889 := by
    simpa [prefixWord, tailWord_4870889, baseEnd_4870889] using wordTrace_append hprefix tailTrace_4870889
  have hstable : (prefixWord ++ tailWord_4870889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870889).length < 2 ^ (prefixWord ++ tailWord_4870889).sum := by decide
  have hdescent : baseEnd_4870889 < baseStart_4870889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870910 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_4870910 : Nat := 118140960795 + 4870910 * 2 ^ 59
def prefixEnd_4870910 : Nat := 4983230072969 + 3 ^ 40 * 4870910 * 2
def baseEnd_4870910 : Nat := 277902006087960308436011

theorem tailTrace_4870910 : CollatzResearch.WordTrace tailWord_4870910 prefixEnd_4870910 277902006087960308436011 := by
  unfold tailWord_4870910
  simp only [CollatzResearch.WordTrace]
  refine ⟨22207085347941553755418273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118437788522354953362230789 22207085347941553755418273)
  ·
    refine ⟨16655314010956165316563705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22207085347941553755418273 16655314010956165316563705)
    ·
      refine ⟨12491485508217123987422779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16655314010956165316563705 12491485508217123987422779)
      ·
        refine ⟨18737228262325685981134169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12491485508217123987422779 18737228262325685981134169)
        ·
          refine ⟨14052921196744264485850627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18737228262325685981134169 14052921196744264485850627)
          ·
            refine ⟨21079381795116396728775941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14052921196744264485850627 21079381795116396728775941)
            ·
              refine ⟨3952384086584324386645489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21079381795116396728775941 3952384086584324386645489)
              ·
                refine ⟨2964288064938243289984117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3952384086584324386645489 2964288064938243289984117)
                ·
                  refine ⟨277902006087960308436011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2964288064938243289984117 277902006087960308436011)
                  ·
                    rfl

theorem cell23_4870910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_4870910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870910 prefixEnd_4870910 := by exact prefixLift 4870910
  have htrace : WordTrace (prefixWord ++ tailWord_4870910) baseStart_4870910 baseEnd_4870910 := by
    simpa [prefixWord, tailWord_4870910, baseEnd_4870910] using wordTrace_append hprefix tailTrace_4870910
  have hstable : (prefixWord ++ tailWord_4870910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870910).length < 2 ^ (prefixWord ++ tailWord_4870910).sum := by decide
  have hdescent : baseEnd_4870910 < baseStart_4870910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870943 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 4]
def baseStart_4870943 : Nat := 118140960795 + 4870943 * 2 ^ 59
def prefixEnd_4870943 : Nat := 4983230072969 + 3 ^ 40 * 4870943 * 2
def baseEnd_4870943 : Nat := 2501134999653241146811447

theorem tailTrace_4870943 : CollatzResearch.WordTrace tailWord_4870943 prefixEnd_4870943 2501134999653241146811447 := by
  unfold tailWord_4870943
  simp only [CollatzResearch.WordTrace]
  refine ⟨177657886392412876679297483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118438590928275251119531655 177657886392412876679297483)
  ·
    refine ⟨266486829588619315018946225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177657886392412876679297483 266486829588619315018946225)
    ·
      refine ⟨199865122191464486264209669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266486829588619315018946225 199865122191464486264209669)
      ·
        refine ⟨37474710410899591174539313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199865122191464486264209669 37474710410899591174539313)
        ·
          refine ⟨28106032808174693380904485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37474710410899591174539313 28106032808174693380904485)
          ·
            refine ⟨5269881151532755008919591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28106032808174693380904485 5269881151532755008919591)
            ·
              refine ⟨7904821727299132513379387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5269881151532755008919591 7904821727299132513379387)
              ·
                refine ⟨11857232590948698770069081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7904821727299132513379387 11857232590948698770069081)
                ·
                  refine ⟨8892924443211524077551811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11857232590948698770069081 8892924443211524077551811)
                  ·
                    refine ⟨13339386664817286116327717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8892924443211524077551811 13339386664817286116327717)
                    ·
                      refine ⟨2501134999653241146811447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13339386664817286116327717 2501134999653241146811447)
                      ·
                        rfl

theorem cell23_4870943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_4870943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870943 prefixEnd_4870943 := by exact prefixLift 4870943
  have htrace : WordTrace (prefixWord ++ tailWord_4870943) baseStart_4870943 baseEnd_4870943 := by
    simpa [prefixWord, tailWord_4870943, baseEnd_4870943] using wordTrace_append hprefix tailTrace_4870943
  have hstable : (prefixWord ++ tailWord_4870943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870943).length < 2 ^ (prefixWord ++ tailWord_4870943).sum := by decide
  have hdescent : baseEnd_4870943 < baseStart_4870943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4870949 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 8]
def baseStart_4870949 : Nat := 118140960795 + 4870949 * 2 ^ 59
def prefixEnd_4870949 : Nat := 4983230072969 + 3 ^ 40 * 4870949 * 2
def baseEnd_4870949 : Nat := 277904231170796458148491

theorem tailTrace_4870949 : CollatzResearch.WordTrace tailWord_4870949 prefixEnd_4870949 277904231170796458148491 := by
  unfold tailWord_4870949
  simp only [CollatzResearch.WordTrace]
  refine ⟨177658105230391139704015901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118438736820260759802677267 177658105230391139704015901)
  ·
    refine ⟨66621789461396677389005963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177658105230391139704015901 66621789461396677389005963)
    ·
      refine ⟨99932684192095016083508945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66621789461396677389005963 99932684192095016083508945)
      ·
        refine ⟨74949513144071262062631709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99932684192095016083508945 74949513144071262062631709)
        ·
          refine ⟨28106067429026723273486891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74949513144071262062631709 28106067429026723273486891)
          ·
            refine ⟨42159101143540084910230337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28106067429026723273486891 42159101143540084910230337)
            ·
              refine ⟨31619325857655063682672753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42159101143540084910230337 31619325857655063682672753)
              ·
                refine ⟨23714494393241297762004565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31619325857655063682672753 23714494393241297762004565)
                ·
                  refine ⟨277904231170796458148491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23714494393241297762004565 277904231170796458148491)
                  ·
                    rfl

theorem cell23_4870949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_4870949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4870949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4870949 prefixEnd_4870949 := by exact prefixLift 4870949
  have htrace : WordTrace (prefixWord ++ tailWord_4870949) baseStart_4870949 baseEnd_4870949 := by
    simpa [prefixWord, tailWord_4870949, baseEnd_4870949] using wordTrace_append hprefix tailTrace_4870949
  have hstable : (prefixWord ++ tailWord_4870949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4870949).length < 2 ^ (prefixWord ++ tailWord_4870949).sum := by decide
  have hdescent : baseEnd_4870949 < baseStart_4870949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4870949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871039 : List Nat := [1, 1, 2, 2, 1, 1, 5, 10]
def baseStart_4871039 : Nat := 118140960795 + 4871039 * 2 ^ 59
def prefixEnd_4871039 : Nat := 4983230072969 + 3 ^ 40 * 4871039 * 2
def baseEnd_4871039 : Nat := 92636455325780473007815

theorem tailTrace_4871039 : CollatzResearch.WordTrace tailWord_4871039 prefixEnd_4871039 92636455325780473007815 := by
  unfold tailWord_4871039
  simp only [CollatzResearch.WordTrace]
  refine ⟨177661387800065085074792171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118440925200043390049861447 177661387800065085074792171)
  ·
    refine ⟨266492081700097627612188257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177661387800065085074792171 266492081700097627612188257)
    ·
      refine ⟨199869061275073220709141193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266492081700097627612188257 199869061275073220709141193)
      ·
        refine ⟨149901795956304915531855895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199869061275073220709141193 149901795956304915531855895)
        ·
          refine ⟨224852693934457373297783843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149901795956304915531855895 224852693934457373297783843)
          ·
            refine ⟨337279040901686059946675765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224852693934457373297783843 337279040901686059946675765)
            ·
              refine ⟨31619910084533068120000853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337279040901686059946675765 31619910084533068120000853)
              ·
                refine ⟨92636455325780473007815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31619910084533068120000853 92636455325780473007815)
                ·
                  rfl

theorem cell23_4871039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 10].length) (baseStart_4871039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871039 prefixEnd_4871039 := by exact prefixLift 4871039
  have htrace : WordTrace (prefixWord ++ tailWord_4871039) baseStart_4871039 baseEnd_4871039 := by
    simpa [prefixWord, tailWord_4871039, baseEnd_4871039] using wordTrace_append hprefix tailTrace_4871039
  have hstable : (prefixWord ++ tailWord_4871039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871039).length < 2 ^ (prefixWord ++ tailWord_4871039).sum := by decide
  have hdescent : baseEnd_4871039 < baseStart_4871039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871043 : List Nat := [1, 1, 1, 3, 4, 1, 3, 3, 2, 4]
def baseStart_4871043 : Nat := 118140960795 + 4871043 * 2 ^ 59
def prefixEnd_4871043 : Nat := 4983230072969 + 3 ^ 40 * 4871043 * 2
def baseEnd_4871043 : Nat := 833728782572896918520329

theorem tailTrace_4871043 : CollatzResearch.WordTrace tailWord_4871043 prefixEnd_4871043 833728782572896918520329 := by
  unfold tailWord_4871043
  simp only [CollatzResearch.WordTrace]
  refine ⟨177661533692050593757937783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118441022461367062505291855 177661533692050593757937783)
  ·
    refine ⟨266492300538075890636906675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177661533692050593757937783 266492300538075890636906675)
    ·
      refine ⟨399738450807113835955360013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266492300538075890636906675 399738450807113835955360013)
      ·
        refine ⟨149901919052667688483260005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 399738450807113835955360013 149901919052667688483260005)
        ·
          refine ⟨28106609822375191590611251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149901919052667688483260005 28106609822375191590611251)
          ·
            refine ⟨42159914733562787385916877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28106609822375191590611251 42159914733562787385916877)
            ·
              refine ⟨15809968025086045269718829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42159914733562787385916877 15809968025086045269718829)
              ·
                refine ⟨5928738009407266976144561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15809968025086045269718829 5928738009407266976144561)
                ·
                  refine ⟨4446553507055450232108421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5928738009407266976144561 4446553507055450232108421)
                  ·
                    refine ⟨833728782572896918520329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4446553507055450232108421 833728782572896918520329)
                    ·
                      rfl

theorem cell23_4871043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 3, 2, 4].length) (baseStart_4871043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871043 prefixEnd_4871043 := by exact prefixLift 4871043
  have htrace : WordTrace (prefixWord ++ tailWord_4871043) baseStart_4871043 baseEnd_4871043 := by
    simpa [prefixWord, tailWord_4871043, baseEnd_4871043] using wordTrace_append hprefix tailTrace_4871043
  have hstable : (prefixWord ++ tailWord_4871043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871043).length < 2 ^ (prefixWord ++ tailWord_4871043).sum := by decide
  have hdescent : baseEnd_4871043 < baseStart_4871043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871050 : List Nat := [3, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4]
def baseStart_4871050 : Nat := 118140960795 + 4871050 * 2 ^ 59
def prefixEnd_4871050 : Nat := 4983230072969 + 3 ^ 40 * 4871050 * 2
def baseEnd_4871050 : Nat := 2501189942083272228173455

theorem tailTrace_4871050 : CollatzResearch.WordTrace tailWord_4871050 prefixEnd_4871050 2501189942083272228173455 := by
  unfold tailWord_4871050
  simp only [CollatzResearch.WordTrace]
  refine ⟨44415447250756308488360651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118441192668683489302295069 44415447250756308488360651)
  ·
    refine ⟨66623170876134462732540977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44415447250756308488360651 66623170876134462732540977)
    ·
      refine ⟨49967378157100847049405733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66623170876134462732540977 49967378157100847049405733)
      ·
        refine ⟨9368883404456408821763575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49967378157100847049405733 9368883404456408821763575)
        ·
          refine ⟨14053325106684613232645363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9368883404456408821763575 14053325106684613232645363)
          ·
            refine ⟨21079987660026919848968045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14053325106684613232645363 21079987660026919848968045)
            ·
              refine ⟨7904995372510094943363017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21079987660026919848968045 7904995372510094943363017)
              ·
                refine ⟨5928746529382571207522263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7904995372510094943363017 5928746529382571207522263)
                ·
                  refine ⟨8893119794073856811283395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5928746529382571207522263 8893119794073856811283395)
                  ·
                    refine ⟨13339679691110785216925093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8893119794073856811283395 13339679691110785216925093)
                    ·
                      refine ⟨2501189942083272228173455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13339679691110785216925093 2501189942083272228173455)
                      ·
                        rfl

theorem cell23_4871050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_4871050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871050 prefixEnd_4871050 := by exact prefixLift 4871050
  have htrace : WordTrace (prefixWord ++ tailWord_4871050) baseStart_4871050 baseEnd_4871050 := by
    simpa [prefixWord, tailWord_4871050, baseEnd_4871050] using wordTrace_append hprefix tailTrace_4871050
  have hstable : (prefixWord ++ tailWord_4871050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871050).length < 2 ^ (prefixWord ++ tailWord_4871050).sum := by decide
  have hdescent : baseEnd_4871050 < baseStart_4871050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871094 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4871094 : Nat := 118140960795 + 4871094 * 2 ^ 59
def prefixEnd_4871094 : Nat := 4983230072969 + 3 ^ 40 * 4871094 * 2
def baseEnd_4871094 : Nat := 833737511744023352007751

theorem tailTrace_4871094 : CollatzResearch.WordTrace tailWord_4871094 prefixEnd_4871094 833737511744023352007751 := by
  unfold tailWord_4871094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103962113429114341752771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118442262543243886312029557 11103962113429114341752771)
  ·
    refine ⟨16655943170143671512629157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11103962113429114341752771 16655943170143671512629157)
    ·
      refine ⟨3122989344401938408617967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16655943170143671512629157 3122989344401938408617967)
      ·
        refine ⟨4684484016602907612926951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3122989344401938408617967 4684484016602907612926951)
        ·
          refine ⟨7026726024904361419390427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4684484016602907612926951 7026726024904361419390427)
          ·
            refine ⟨10540089037356542129085641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7026726024904361419390427 10540089037356542129085641)
            ·
              refine ⟨7905066778017406596814231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10540089037356542129085641 7905066778017406596814231)
              ·
                refine ⟨11857600167026109895221347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905066778017406596814231 11857600167026109895221347)
                ·
                  refine ⟨17786400250539164842832021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11857600167026109895221347 17786400250539164842832021)
                  ·
                    refine ⟨833737511744023352007751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17786400250539164842832021 833737511744023352007751)
                    ·
                      rfl

theorem cell23_4871094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4871094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871094 prefixEnd_4871094 := by exact prefixLift 4871094
  have htrace : WordTrace (prefixWord ++ tailWord_4871094) baseStart_4871094 baseEnd_4871094 := by
    simpa [prefixWord, tailWord_4871094, baseEnd_4871094] using wordTrace_append hprefix tailTrace_4871094
  have hstable : (prefixWord ++ tailWord_4871094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871094).length < 2 ^ (prefixWord ++ tailWord_4871094).sum := by decide
  have hdescent : baseEnd_4871094 < baseStart_4871094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871116 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_4871116 : Nat := 118140960795 + 4871116 * 2 ^ 59
def prefixEnd_4871116 : Nat := 4983230072969 + 3 ^ 40 * 4871116 * 2
def baseEnd_4871116 : Nat := 833741277268822989982717

theorem tailTrace_4871116 : CollatzResearch.WordTrace tailWord_4871116 prefixEnd_4871116 833741277268822989982717 := by
  unfold tailWord_4871116
  simp only [CollatzResearch.WordTrace]
  refine ⟨88832098110393063612672601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118442797480524084816896801 88832098110393063612672601)
  ·
    refine ⟨66624073582794797709504451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88832098110393063612672601 66624073582794797709504451)
    ·
      refine ⟨99936110374192196564256677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66624073582794797709504451 99936110374192196564256677)
      ·
        refine ⟨18738020695161036855798127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99936110374192196564256677 18738020695161036855798127)
        ·
          refine ⟨28107031042741555283697191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18738020695161036855798127 28107031042741555283697191)
          ·
            refine ⟨42160546564112332925545787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28107031042741555283697191 42160546564112332925545787)
            ·
              refine ⟨63240819846168499388318681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42160546564112332925545787 63240819846168499388318681)
              ·
                refine ⟨47430614884626374541239011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63240819846168499388318681 47430614884626374541239011)
                ·
                  refine ⟨71145922326939561811858517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47430614884626374541239011 71145922326939561811858517)
                  ·
                    refine ⟨833741277268822989982717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71145922326939561811858517 833741277268822989982717)
                    ·
                      rfl

theorem cell23_4871116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_4871116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871116 prefixEnd_4871116 := by exact prefixLift 4871116
  have htrace : WordTrace (prefixWord ++ tailWord_4871116) baseStart_4871116 baseEnd_4871116 := by
    simpa [prefixWord, tailWord_4871116, baseEnd_4871116] using wordTrace_append hprefix tailTrace_4871116
  have hstable : (prefixWord ++ tailWord_4871116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871116).length < 2 ^ (prefixWord ++ tailWord_4871116).sum := by decide
  have hdescent : baseEnd_4871116 < baseStart_4871116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871133 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4871133 : Nat := 118140960795 + 4871133 * 2 ^ 59
def prefixEnd_4871133 : Nat := 4983230072969 + 3 ^ 40 * 4871133 * 2
def baseEnd_4871133 : Nat := 833744186992531801145191

theorem tailTrace_4871133 : CollatzResearch.WordTrace tailWord_4871133 prefixEnd_4871133 833744186992531801145191 := by
  unfold tailWord_4871133
  simp only [CollatzResearch.WordTrace]
  refine ⟨177664816261724539128714053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118443210841149692752476035 177664816261724539128714053)
  ·
    refine ⟨33312153049073351086633885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177664816261724539128714053 33312153049073351086633885)
    ·
      refine ⟨12492057393402506657487707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33312153049073351086633885 12492057393402506657487707)
      ·
        refine ⟨18738086090103759986231561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12492057393402506657487707 18738086090103759986231561)
        ·
          refine ⟨14053564567577819989673671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18738086090103759986231561 14053564567577819989673671)
          ·
            refine ⟨21080346851366729984510507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14053564567577819989673671 21080346851366729984510507)
            ·
              refine ⟨31620520277050094976765761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21080346851366729984510507 31620520277050094976765761)
              ·
                refine ⟨23715390207787571232574321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31620520277050094976765761 23715390207787571232574321)
                ·
                  refine ⟨17786542655840678424430741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23715390207787571232574321 17786542655840678424430741)
                  ·
                    refine ⟨833744186992531801145191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17786542655840678424430741 833744186992531801145191)
                    ·
                      rfl

theorem cell23_4871133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4871133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871133 prefixEnd_4871133 := by exact prefixLift 4871133
  have htrace : WordTrace (prefixWord ++ tailWord_4871133) baseStart_4871133 baseEnd_4871133 := by
    simpa [prefixWord, tailWord_4871133, baseEnd_4871133] using wordTrace_append hprefix tailTrace_4871133
  have hstable : (prefixWord ++ tailWord_4871133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871133).length < 2 ^ (prefixWord ++ tailWord_4871133).sum := by decide
  have hdescent : baseEnd_4871133 < baseStart_4871133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871153 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 4]
def baseStart_4871153 : Nat := 118140960795 + 4871153 * 2 ^ 59
def prefixEnd_4871153 : Nat := 4983230072969 + 3 ^ 40 * 4871153 * 2
def baseEnd_4871153 : Nat := 2501242830590685325185481

theorem tailTrace_4871153 : CollatzResearch.WordTrace tailWord_4871153 prefixEnd_4871153 2501242830590685325185481 := by
  unfold tailWord_4871153
  simp only [CollatzResearch.WordTrace]
  refine ⟨177665545721652082544442113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118443697147768055029628075 177665545721652082544442113)
  ·
    refine ⟨133249159291239061908331585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177665545721652082544442113 133249159291239061908331585)
    ·
      refine ⟨99936869468429296431248689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133249159291239061908331585 99936869468429296431248689)
      ·
        refine ⟨74952652101321972323436517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99936869468429296431248689 74952652101321972323436517)
        ·
          refine ⟨14053622268997869810644347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74952652101321972323436517 14053622268997869810644347)
          ·
            refine ⟨21080433403496804715966521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14053622268997869810644347 21080433403496804715966521)
            ·
              refine ⟨15810325052622603536974891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21080433403496804715966521 15810325052622603536974891)
              ·
                refine ⟨23715487578933905305462337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15810325052622603536974891 23715487578933905305462337)
                ·
                  refine ⟨17786615684200428979096753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23715487578933905305462337 17786615684200428979096753)
                  ·
                    refine ⟨13339961763150321734322565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17786615684200428979096753 13339961763150321734322565)
                    ·
                      refine ⟨2501242830590685325185481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13339961763150321734322565 2501242830590685325185481)
                      ·
                        rfl

theorem cell23_4871153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_4871153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871153 prefixEnd_4871153 := by exact prefixLift 4871153
  have htrace : WordTrace (prefixWord ++ tailWord_4871153) baseStart_4871153 baseEnd_4871153 := by
    simpa [prefixWord, tailWord_4871153, baseEnd_4871153] using wordTrace_append hprefix tailTrace_4871153
  have hstable : (prefixWord ++ tailWord_4871153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871153).length < 2 ^ (prefixWord ++ tailWord_4871153).sum := by decide
  have hdescent : baseEnd_4871153 < baseStart_4871153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871180 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 5]
def baseStart_4871180 : Nat := 118140960795 + 4871180 * 2 ^ 59
def prefixEnd_4871180 : Nat := 4983230072969 + 3 ^ 40 * 4871180 * 2
def baseEnd_4871180 : Nat := 277917410507595191060873

theorem tailTrace_4871180 : CollatzResearch.WordTrace tailWord_4871180 prefixEnd_4871180 277917410507595191060873 := by
  unfold tailWord_4871180
  simp only [CollatzResearch.WordTrace]
  refine ⟨88833265246277133077837497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118444353661702844103783329 88833265246277133077837497)
  ·
    refine ⟨66624948934707849808378123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88833265246277133077837497 66624948934707849808378123)
    ·
      refine ⟨99937423402061774712567185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66624948934707849808378123 99937423402061774712567185)
      ·
        refine ⟨74953067551546331034425389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99937423402061774712567185 74953067551546331034425389)
        ·
          refine ⟨28107400331829874137909521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74953067551546331034425389 28107400331829874137909521)
          ·
            refine ⟨21080550248872405603432141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28107400331829874137909521 21080550248872405603432141)
            ·
              refine ⟨7905206343327152101287053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21080550248872405603432141 7905206343327152101287053)
              ·
                refine ⟨2964452378747682037982645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7905206343327152101287053 2964452378747682037982645)
                ·
                  refine ⟨277917410507595191060873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2964452378747682037982645 277917410507595191060873)
                  ·
                    rfl

theorem cell23_4871180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_4871180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871180 prefixEnd_4871180 := by exact prefixLift 4871180
  have htrace : WordTrace (prefixWord ++ tailWord_4871180) baseStart_4871180 baseEnd_4871180 := by
    simpa [prefixWord, tailWord_4871180, baseEnd_4871180] using wordTrace_append hprefix tailTrace_4871180
  have hstable : (prefixWord ++ tailWord_4871180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871180).length < 2 ^ (prefixWord ++ tailWord_4871180).sum := by decide
  have hdescent : baseEnd_4871180 < baseStart_4871180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871183 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 6, 5, 2]
def baseStart_4871183 : Nat := 118140960795 + 4871183 * 2 ^ 59
def prefixEnd_4871183 : Nat := 4983230072969 + 3 ^ 40 * 4871183 * 2
def baseEnd_4871183 : Nat := 2501258235010320207810343

theorem tailTrace_4871183 : CollatzResearch.WordTrace tailWord_4871183 prefixEnd_4871183 2501258235010320207810343 := by
  unfold tailWord_4871183
  simp only [CollatzResearch.WordTrace]
  refine ⟨177666639911543397668034203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118444426607695598445356135 177666639911543397668034203)
  ·
    refine ⟨266499959867315096502051305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177666639911543397668034203 266499959867315096502051305)
    ·
      refine ⟨199874969900486322376538479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266499959867315096502051305 199874969900486322376538479)
      ·
        refine ⟨299812454850729483564807719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199874969900486322376538479 299812454850729483564807719)
        ·
          refine ⟨449718682276094225347211579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299812454850729483564807719 449718682276094225347211579)
          ·
            refine ⟨674578023414141338020817369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449718682276094225347211579 674578023414141338020817369)
            ·
              refine ⟨505933517560606003515613027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674578023414141338020817369 505933517560606003515613027)
              ·
                refine ⟨758900276340909005273419541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505933517560606003515613027 758900276340909005273419541)
                ·
                  refine ⟨35573450453480109622191541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 758900276340909005273419541 35573450453480109622191541)
                  ·
                    refine ⟨3335010980013760277080457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35573450453480109622191541 3335010980013760277080457)
                    ·
                      refine ⟨2501258235010320207810343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335010980013760277080457 2501258235010320207810343)
                      ·
                        rfl

theorem cell23_4871183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 5, 2].length) (baseStart_4871183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871183 prefixEnd_4871183 := by exact prefixLift 4871183
  have htrace : WordTrace (prefixWord ++ tailWord_4871183) baseStart_4871183 baseEnd_4871183 := by
    simpa [prefixWord, tailWord_4871183, baseEnd_4871183] using wordTrace_append hprefix tailTrace_4871183
  have hstable : (prefixWord ++ tailWord_4871183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871183).length < 2 ^ (prefixWord ++ tailWord_4871183).sum := by decide
  have hdescent : baseEnd_4871183 < baseStart_4871183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871197 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 7]
def baseStart_4871197 : Nat := 118140960795 + 4871197 * 2 ^ 59
def prefixEnd_4871197 : Nat := 4983230072969 + 3 ^ 40 * 4871197 * 2
def baseEnd_4871197 : Nat := 277918380415498128115031

theorem tailTrace_4871197 : CollatzResearch.WordTrace tailWord_4871197 prefixEnd_4871197 277918380415498128115031 := by
  unfold tailWord_4871197
  simp only [CollatzResearch.WordTrace]
  refine ⟨177667150533492678059043845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118444767022328452039362563 177667150533492678059043845)
  ·
    refine ⟨33312590725029877136070721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177667150533492678059043845 33312590725029877136070721)
    ·
      refine ⟨24984443043772407852053041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33312590725029877136070721 24984443043772407852053041)
      ·
        refine ⟨18738332282829305889039781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24984443043772407852053041 18738332282829305889039781)
        ·
          refine ⟨3513437303030494854194959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18738332282829305889039781 3513437303030494854194959)
          ·
            refine ⟨5270155954545742281292439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513437303030494854194959 5270155954545742281292439)
            ·
              refine ⟨7905233931818613421938659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270155954545742281292439 7905233931818613421938659)
              ·
                refine ⟨11857850897727920132907989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905233931818613421938659 11857850897727920132907989)
                ·
                  refine ⟨277918380415498128115031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11857850897727920132907989 277918380415498128115031)
                  ·
                    rfl

theorem cell23_4871197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_4871197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871197 prefixEnd_4871197 := by exact prefixLift 4871197
  have htrace : WordTrace (prefixWord ++ tailWord_4871197) baseStart_4871197 baseEnd_4871197 := by
    simpa [prefixWord, tailWord_4871197, baseEnd_4871197] using wordTrace_append hprefix tailTrace_4871197
  have hstable : (prefixWord ++ tailWord_4871197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871197).length < 2 ^ (prefixWord ++ tailWord_4871197).sum := by decide
  have hdescent : baseEnd_4871197 < baseStart_4871197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871203 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5]
def baseStart_4871203 : Nat := 118140960795 + 4871203 * 2 ^ 59
def prefixEnd_4871203 : Nat := 4983230072969 + 3 ^ 40 * 4871203 * 2
def baseEnd_4871203 : Nat := 2501268504623410129560251

theorem tailTrace_4871203 : CollatzResearch.WordTrace tailWord_4871203 prefixEnd_4871203 2501268504623410129560251 := by
  unfold tailWord_4871203
  simp only [CollatzResearch.WordTrace]
  refine ⟨177667369371470941083762263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118444912914313960722508175 177667369371470941083762263)
  ·
    refine ⟨266501054057206411625643395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177667369371470941083762263 266501054057206411625643395)
    ·
      refine ⟨399751581085809617438465093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266501054057206411625643395 399751581085809617438465093)
      ·
        refine ⟨74953421453589303269712205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399751581085809617438465093 74953421453589303269712205)
        ·
          refine ⟨28107533045095988726142077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74953421453589303269712205 28107533045095988726142077)
          ·
            refine ⟨10540324891910995772303279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28107533045095988726142077 10540324891910995772303279)
            ·
              refine ⟨15810487337866493658454919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10540324891910995772303279 15810487337866493658454919)
              ·
                refine ⟨23715731006799740487682379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15810487337866493658454919 23715731006799740487682379)
                ·
                  refine ⟨35573596510199610731523569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23715731006799740487682379 35573596510199610731523569)
                  ·
                    refine ⟨26680197382649708048642677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35573596510199610731523569 26680197382649708048642677)
                    ·
                      refine ⟨2501268504623410129560251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26680197382649708048642677 2501268504623410129560251)
                      ·
                        rfl

theorem cell23_4871203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_4871203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871203 prefixEnd_4871203 := by exact prefixLift 4871203
  have htrace : WordTrace (prefixWord ++ tailWord_4871203) baseStart_4871203 baseEnd_4871203 := by
    simpa [prefixWord, tailWord_4871203, baseEnd_4871203] using wordTrace_append hprefix tailTrace_4871203
  have hstable : (prefixWord ++ tailWord_4871203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871203).length < 2 ^ (prefixWord ++ tailWord_4871203).sum := by decide
  have hdescent : baseEnd_4871203 < baseStart_4871203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871223 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 5, 4]
def baseStart_4871223 : Nat := 118140960795 + 4871223 * 2 ^ 59
def prefixEnd_4871223 : Nat := 4983230072969 + 3 ^ 40 * 4871223 * 2
def baseEnd_4871223 : Nat := 833759591412166683770053

theorem tailTrace_4871223 : CollatzResearch.WordTrace tailWord_4871223 prefixEnd_4871223 833759591412166683770053 := by
  unfold tailWord_4871223
  simp only [CollatzResearch.WordTrace]
  refine ⟨177668098831398484499490323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118445399220932322999660215 177668098831398484499490323)
  ·
    refine ⟨266502148247097726749235485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177668098831398484499490323 266502148247097726749235485)
    ·
      refine ⟨99938305592661647530963307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266502148247097726749235485 99938305592661647530963307)
      ·
        refine ⟨149907458388992471296444961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99938305592661647530963307 149907458388992471296444961)
        ·
          refine ⟨112430593791744353472333721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149907458388992471296444961 112430593791744353472333721)
          ·
            refine ⟨84322945343808265104250291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112430593791744353472333721 84322945343808265104250291)
            ·
              refine ⟨126484418015712397656375437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84322945343808265104250291 126484418015712397656375437)
              ·
                refine ⟨47431656755892149121140789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126484418015712397656375437 47431656755892149121140789)
                ·
                  refine ⟨4446717820864888980106949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47431656755892149121140789 4446717820864888980106949)
                  ·
                    refine ⟨833759591412166683770053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4446717820864888980106949 833759591412166683770053)
                    ·
                      rfl

theorem cell23_4871223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_4871223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871223 prefixEnd_4871223 := by exact prefixLift 4871223
  have htrace : WordTrace (prefixWord ++ tailWord_4871223) baseStart_4871223 baseEnd_4871223 := by
    simpa [prefixWord, tailWord_4871223, baseEnd_4871223] using wordTrace_append hprefix tailTrace_4871223
  have hstable : (prefixWord ++ tailWord_4871223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871223).length < 2 ^ (prefixWord ++ tailWord_4871223).sum := by decide
  have hdescent : baseEnd_4871223 < baseStart_4871223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871304 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 6]
def baseStart_4871304 : Nat := 118140960795 + 4871304 * 2 ^ 59
def prefixEnd_4871304 : Nat := 4983230072969 + 3 ^ 40 * 4871304 * 2
def baseEnd_4871304 : Nat := 277924485129946026044143

theorem tailTrace_4871304 : CollatzResearch.WordTrace tailWord_4871304 prefixEnd_4871304 277924485129946026044143 := by
  unfold tailWord_4871304
  simp only [CollatzResearch.WordTrace]
  refine ⟨88835526572052517666594483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118447368762736690222125977 88835526572052517666594483)
  ·
    refine ⟨133253289858078776499891725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88835526572052517666594483 133253289858078776499891725)
    ·
      refine ⟨49969983696779541187459397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133253289858078776499891725 49969983696779541187459397)
      ·
        refine ⟨9369371943146163972648637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49969983696779541187459397 9369371943146163972648637)
        ·
          refine ⟨3513514478679811489743239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9369371943146163972648637 3513514478679811489743239)
          ·
            refine ⟨5270271718019717234614859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3513514478679811489743239 5270271718019717234614859)
            ·
              refine ⟨7905407577029575851922289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270271718019717234614859 7905407577029575851922289)
              ·
                refine ⟨5929055682772181888941717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7905407577029575851922289 5929055682772181888941717)
                ·
                  refine ⟨277924485129946026044143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5929055682772181888941717 277924485129946026044143)
                  ·
                    rfl

theorem cell23_4871304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 6].length) (baseStart_4871304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871304 prefixEnd_4871304 := by exact prefixLift 4871304
  have htrace : WordTrace (prefixWord ++ tailWord_4871304) baseStart_4871304 baseEnd_4871304 := by
    simpa [prefixWord, tailWord_4871304, baseEnd_4871304] using wordTrace_append hprefix tailTrace_4871304
  have hstable : (prefixWord ++ tailWord_4871304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871304).length < 2 ^ (prefixWord ++ tailWord_4871304).sum := by decide
  have hdescent : baseEnd_4871304 < baseStart_4871304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871314 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_4871314 : Nat := 118140960795 + 4871314 * 2 ^ 59
def prefixEnd_4871314 : Nat := 4983230072969 + 3 ^ 40 * 4871314 * 2
def baseEnd_4871314 : Nat := 2501325500976059195272241

theorem tailTrace_4871314 : CollatzResearch.WordTrace tailWord_4871314 prefixEnd_4871314 2501325500976059195272241 := by
  unfold tailWord_4871314
  simp only [CollatzResearch.WordTrace]
  refine ⟨44417854468517201760263249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118447611916045871360701997 44417854468517201760263249)
  ·
    refine ⟨33313390851387901320197437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44417854468517201760263249 33313390851387901320197437)
    ·
      refine ⟨12492521569270462995074039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33313390851387901320197437 12492521569270462995074039)
      ·
        refine ⟨18738782353905694492611059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12492521569270462995074039 18738782353905694492611059)
        ·
          refine ⟨28108173530858541738916589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18738782353905694492611059 28108173530858541738916589)
          ·
            refine ⟨10540565074071953152093721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28108173530858541738916589 10540565074071953152093721)
            ·
              refine ⟨7905423805553964864070291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10540565074071953152093721 7905423805553964864070291)
              ·
                refine ⟨11858135708330947296105437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905423805553964864070291 11858135708330947296105437)
                ·
                  refine ⟨4446800890624105236039539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11858135708330947296105437 4446800890624105236039539)
                  ·
                    refine ⟨6670201335936157854059309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4446800890624105236039539 6670201335936157854059309)
                    ·
                      refine ⟨2501325500976059195272241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670201335936157854059309 2501325500976059195272241)
                      ·
                        rfl

theorem cell23_4871314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_4871314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871314 prefixEnd_4871314 := by exact prefixLift 4871314
  have htrace : WordTrace (prefixWord ++ tailWord_4871314) baseStart_4871314 baseEnd_4871314 := by
    simpa [prefixWord, tailWord_4871314, baseEnd_4871314] using wordTrace_append hprefix tailTrace_4871314
  have hstable : (prefixWord ++ tailWord_4871314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871314).length < 2 ^ (prefixWord ++ tailWord_4871314).sum := by decide
  have hdescent : baseEnd_4871314 < baseStart_4871314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871323 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3]
def baseStart_4871323 : Nat := 118140960795 + 4871323 * 2 ^ 59
def prefixEnd_4871323 : Nat := 4983230072969 + 3 ^ 40 * 4871323 * 2
def baseEnd_4871323 : Nat := 2501330122301949660059699

theorem tailTrace_4871323 : CollatzResearch.WordTrace tailWord_4871323 prefixEnd_4871323 2501330122301949660059699 := by
  unfold tailWord_4871323
  simp only [CollatzResearch.WordTrace]
  refine ⟨177671746131036201578130623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118447830754024134385420415 177671746131036201578130623)
  ·
    refine ⟨266507619196554302367195935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177671746131036201578130623 266507619196554302367195935)
    ·
      refine ⟨399761428794831453550793903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266507619196554302367195935 399761428794831453550793903)
      ·
        refine ⟨599642143192247180326190855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399761428794831453550793903 599642143192247180326190855)
        ·
          refine ⟨899463214788370770489286283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599642143192247180326190855 899463214788370770489286283)
          ·
            refine ⟨1349194822182556155733929425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899463214788370770489286283 1349194822182556155733929425)
            ·
              refine ⟨1011896116636917116800447069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349194822182556155733929425 1011896116636917116800447069)
              ·
                refine ⟨379461043738843918800167651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011896116636917116800447069 379461043738843918800167651)
                ·
                  refine ⟨569191565608265878200251477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379461043738843918800167651 569191565608265878200251477)
                  ·
                    refine ⟨6670213659471865760159197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 569191565608265878200251477 6670213659471865760159197)
                    ·
                      refine ⟨2501330122301949660059699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670213659471865760159197 2501330122301949660059699)
                      ·
                        rfl

theorem cell23_4871323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 3].length) (baseStart_4871323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871323 prefixEnd_4871323 := by exact prefixLift 4871323
  have htrace : WordTrace (prefixWord ++ tailWord_4871323) baseStart_4871323 baseEnd_4871323 := by
    simpa [prefixWord, tailWord_4871323, baseEnd_4871323] using wordTrace_append hprefix tailTrace_4871323
  have hstable : (prefixWord ++ tailWord_4871323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871323).length < 2 ^ (prefixWord ++ tailWord_4871323).sum := by decide
  have hdescent : baseEnd_4871323 < baseStart_4871323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871357 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 3]
def baseStart_4871357 : Nat := 118140960795 + 4871357 * 2 ^ 59
def prefixEnd_4871357 : Nat := 4983230072969 + 3 ^ 40 * 4871357 * 2
def baseEnd_4871357 : Nat := 2501347580644202527034543

theorem tailTrace_4871357 : CollatzResearch.WordTrace tailWord_4871357 prefixEnd_4871357 2501347580644202527034543 := by
  unfold tailWord_4871357
  simp only [CollatzResearch.WordTrace]
  refine ⟨177672986212913025384868325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118448657475275350256578883 177672986212913025384868325)
  ·
    refine ⟨33313684914921192259662811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177672986212913025384868325 33313684914921192259662811)
    ·
      refine ⟨49970527372381788389494217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33313684914921192259662811 49970527372381788389494217)
      ·
        refine ⟨37477895529286341292120663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49970527372381788389494217 37477895529286341292120663)
        ·
          refine ⟨56216843293929511938180995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37477895529286341292120663 56216843293929511938180995)
          ·
            refine ⟨84325264940894267907271493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56216843293929511938180995 84325264940894267907271493)
            ·
              refine ⟨15810987176417675232613405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84325264940894267907271493 15810987176417675232613405)
              ·
                refine ⟨5929120191156628212230027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15810987176417675232613405 5929120191156628212230027)
                ·
                  refine ⟨8893680286734942318345041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929120191156628212230027 8893680286734942318345041)
                  ·
                    refine ⟨6670260215051206738758781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8893680286734942318345041 6670260215051206738758781)
                    ·
                      refine ⟨2501347580644202527034543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670260215051206738758781 2501347580644202527034543)
                      ·
                        rfl

theorem cell23_4871357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_4871357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871357 prefixEnd_4871357 := by exact prefixLift 4871357
  have htrace : WordTrace (prefixWord ++ tailWord_4871357) baseStart_4871357 baseEnd_4871357 := by
    simpa [prefixWord, tailWord_4871357, baseEnd_4871357] using wordTrace_append hprefix tailTrace_4871357
  have hstable : (prefixWord ++ tailWord_4871357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871357).length < 2 ^ (prefixWord ++ tailWord_4871357).sum := by decide
  have hdescent : baseEnd_4871357 < baseStart_4871357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871360 : List Nat := [2, 1, 1, 2, 6, 2, 9]
def baseStart_4871360 : Nat := 118140960795 + 4871360 * 2 ^ 59
def prefixEnd_4871360 : Nat := 4983230072969 + 3 ^ 40 * 4871360 * 2
def baseEnd_4871360 : Nat := 30880853346742790312309

theorem tailTrace_4871360 : CollatzResearch.WordTrace tailWord_4871360 prefixEnd_4871360 30880853346742790312309 := by
  unfold tailWord_4871360
  simp only [CollatzResearch.WordTrace]
  refine ⟨88836547815951078448613767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118448730421268104598151689 88836547815951078448613767)
  ·
    refine ⟨133254821723926617672920651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88836547815951078448613767 133254821723926617672920651)
    ·
      refine ⟨199882232585889926509380977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133254821723926617672920651 199882232585889926509380977)
      ·
        refine ⟨149911674439417444882035733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199882232585889926509380977 149911674439417444882035733)
        ·
          refine ⟨7027109739347692728845425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149911674439417444882035733 7027109739347692728845425)
          ·
            refine ⟨5270332304510769546634069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027109739347692728845425 5270332304510769546634069)
            ·
              refine ⟨30880853346742790312309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5270332304510769546634069 30880853346742790312309)
              ·
                rfl

theorem cell23_4871360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 2, 9].length) (baseStart_4871360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871360 prefixEnd_4871360 := by exact prefixLift 4871360
  have htrace : WordTrace (prefixWord ++ tailWord_4871360) baseStart_4871360 baseEnd_4871360 := by
    simpa [prefixWord, tailWord_4871360, baseEnd_4871360] using wordTrace_append hprefix tailTrace_4871360
  have hstable : (prefixWord ++ tailWord_4871360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871360).length < 2 ^ (prefixWord ++ tailWord_4871360).sum := by decide
  have hdescent : baseEnd_4871360 < baseStart_4871360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871381 : List Nat := [1, 3, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_4871381 : Nat := 118140960795 + 4871381 * 2 ^ 59
def prefixEnd_4871381 : Nat := 4983230072969 + 3 ^ 40 * 4871381 * 2
def baseEnd_4871381 : Nat := 833786634726636811044811

theorem tailTrace_4871381 : CollatzResearch.WordTrace tailWord_4871381 prefixEnd_4871381 833786634726636811044811 := by
  unfold tailWord_4871381
  simp only [CollatzResearch.WordTrace]
  refine ⟨177673861564826077483741997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118449241043217384989161331 177673861564826077483741997)
  ·
    refine ⟨66627698086809779056403249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177673861564826077483741997 66627698086809779056403249)
    ·
      refine ⟨49970773565107334292302437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66627698086809779056403249 49970773565107334292302437)
      ·
        refine ⟨9369520043457625179806707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49970773565107334292302437 9369520043457625179806707)
        ·
          refine ⟨14054280065186437769710061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9369520043457625179806707 14054280065186437769710061)
          ·
            refine ⟨5270355024444914163641273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14054280065186437769710061 5270355024444914163641273)
            ·
              refine ⟨3952766268333685622730955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5270355024444914163641273 3952766268333685622730955)
              ·
                refine ⟨5929149402500528434096433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952766268333685622730955 5929149402500528434096433)
                ·
                  refine ⟨4446862051875396325572325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5929149402500528434096433 4446862051875396325572325)
                  ·
                    refine ⟨833786634726636811044811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4446862051875396325572325 833786634726636811044811)
                    ·
                      rfl

theorem cell23_4871381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_4871381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871381 prefixEnd_4871381 := by exact prefixLift 4871381
  have htrace : WordTrace (prefixWord ++ tailWord_4871381) baseStart_4871381 baseEnd_4871381 := by
    simpa [prefixWord, tailWord_4871381, baseEnd_4871381] using wordTrace_append hprefix tailTrace_4871381
  have hstable : (prefixWord ++ tailWord_4871381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871381).length < 2 ^ (prefixWord ++ tailWord_4871381).sum := by decide
  have hdescent : baseEnd_4871381 < baseStart_4871381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871450 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 9]
def baseStart_4871450 : Nat := 118140960795 + 4871450 * 2 ^ 59
def prefixEnd_4871450 : Nat := 4983230072969 + 3 ^ 40 * 4871450 * 2
def baseEnd_4871450 : Nat := 277932814927230073685735

theorem tailTrace_4871450 : CollatzResearch.WordTrace tailWord_4871450 prefixEnd_4871450 277932814927230073685735 := by
  unfold tailWord_4871450
  simp only [CollatzResearch.WordTrace]
  refine ⟨44419094550394025567000951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118450918801050734845335869 44419094550394025567000951)
  ·
    refine ⟨66628641825591038350501427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44419094550394025567000951 66628641825591038350501427)
    ·
      refine ⟨99942962738386557525752141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66628641825591038350501427 99942962738386557525752141)
      ·
        refine ⟨37478611026894959072157053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99942962738386557525752141 37478611026894959072157053)
        ·
          refine ⟨14054479135085609652058895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37478611026894959072157053 14054479135085609652058895)
          ·
            refine ⟨21081718702628414478088343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14054479135085609652058895 21081718702628414478088343)
            ·
              refine ⟨31622578053942621717132515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21081718702628414478088343 31622578053942621717132515)
              ·
                refine ⟨47433867080913932575698773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31622578053942621717132515 47433867080913932575698773)
                ·
                  refine ⟨277932814927230073685735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47433867080913932575698773 277932814927230073685735)
                  ·
                    rfl

theorem cell23_4871450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_4871450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871450 prefixEnd_4871450 := by exact prefixLift 4871450
  have htrace : WordTrace (prefixWord ++ tailWord_4871450) baseStart_4871450 baseEnd_4871450 := by
    simpa [prefixWord, tailWord_4871450, baseEnd_4871450] using wordTrace_append hprefix tailTrace_4871450
  have hstable : (prefixWord ++ tailWord_4871450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871450).length < 2 ^ (prefixWord ++ tailWord_4871450).sum := by decide
  have hdescent : baseEnd_4871450 < baseStart_4871450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871477 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_4871477 : Nat := 118140960795 + 4871477 * 2 ^ 59
def prefixEnd_4871477 : Nat := 4983230072969 + 3 ^ 40 * 4871477 * 2
def baseEnd_4871477 : Nat := 2501409198322742057533991

theorem tailTrace_4871477 : CollatzResearch.WordTrace tailWord_4871477 prefixEnd_4871477 2501409198322742057533991 := by
  unfold tailWord_4871477
  simp only [CollatzResearch.WordTrace]
  refine ⟨177677362972478285879236685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118451575314985523919491123 177677362972478285879236685)
  ·
    refine ⟨66629011114679357204713757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177677362972478285879236685 66629011114679357204713757)
    ·
      refine ⟨24985879168004758951767659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66629011114679357204713757 24985879168004758951767659)
      ·
        refine ⟨37478818752007138427651489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24985879168004758951767659 37478818752007138427651489)
        ·
          refine ⟨28109114064005353820738617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37478818752007138427651489 28109114064005353820738617)
          ·
            refine ⟨21081835548004015365553963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28109114064005353820738617 21081835548004015365553963)
            ·
              refine ⟨31622753322006023048330945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21081835548004015365553963 31622753322006023048330945)
              ·
                refine ⟨23717064991504517286248209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31622753322006023048330945 23717064991504517286248209)
                ·
                  refine ⟨17787798743628387964686157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23717064991504517286248209 17787798743628387964686157)
                  ·
                    refine ⟨6670424528860645486757309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17787798743628387964686157 6670424528860645486757309)
                    ·
                      refine ⟨2501409198322742057533991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670424528860645486757309 2501409198322742057533991)
                      ·
                        rfl

theorem cell23_4871477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_4871477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871477 prefixEnd_4871477 := by exact prefixLift 4871477
  have htrace : WordTrace (prefixWord ++ tailWord_4871477) baseStart_4871477 baseEnd_4871477 := by
    simpa [prefixWord, tailWord_4871477, baseEnd_4871477] using wordTrace_append hprefix tailTrace_4871477
  have hstable : (prefixWord ++ tailWord_4871477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871477).length < 2 ^ (prefixWord ++ tailWord_4871477).sum := by decide
  have hdescent : baseEnd_4871477 < baseStart_4871477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871480 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 4, 5]
def baseStart_4871480 : Nat := 118140960795 + 4871480 * 2 ^ 59
def prefixEnd_4871480 : Nat := 4983230072969 + 3 ^ 40 * 4871480 * 2
def baseEnd_4871480 : Nat := 833803579588235181932159

theorem tailTrace_4871480 : CollatzResearch.WordTrace tailWord_4871480 prefixEnd_4871480 833803579588235181932159 := by
  unfold tailWord_4871480
  simp only [CollatzResearch.WordTrace]
  refine ⟨88838736195733708695797947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118451648260978278261063929 88838736195733708695797947)
  ·
    refine ⟨133258104293600563043696921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88838736195733708695797947 133258104293600563043696921)
    ·
      refine ⟨99943578220200422282772691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133258104293600563043696921 99943578220200422282772691)
      ·
        refine ⟨149915367330300633424159037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99943578220200422282772691 149915367330300633424159037)
        ·
          refine ⟨56218262748862737534059639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149915367330300633424159037 56218262748862737534059639)
          ·
            refine ⟨84327394123294106301089459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56218262748862737534059639 84327394123294106301089459)
            ·
              refine ⟨126491091184941159451634189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84327394123294106301089459 126491091184941159451634189)
              ·
                refine ⟨47434159194352934794362821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126491091184941159451634189 47434159194352934794362821)
                ·
                  refine ⟨8893904848941175273943029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47434159194352934794362821 8893904848941175273943029)
                  ·
                    refine ⟨833803579588235181932159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8893904848941175273943029 833803579588235181932159)
                    ·
                      rfl

theorem cell23_4871480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 4, 5].length) (baseStart_4871480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871480 prefixEnd_4871480 := by exact prefixLift 4871480
  have htrace : WordTrace (prefixWord ++ tailWord_4871480) baseStart_4871480 baseEnd_4871480 := by
    simpa [prefixWord, tailWord_4871480, baseEnd_4871480] using wordTrace_append hprefix tailTrace_4871480
  have hstable : (prefixWord ++ tailWord_4871480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871480).length < 2 ^ (prefixWord ++ tailWord_4871480).sum := by decide
  have hdescent : baseEnd_4871480 < baseStart_4871480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871537 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 3]
def baseStart_4871537 : Nat := 118140960795 + 4871537 * 2 ^ 59
def prefixEnd_4871537 : Nat := 4983230072969 + 3 ^ 40 * 4871537 * 2
def baseEnd_4871537 : Nat := 2501440007162011822783715

theorem tailTrace_4871537 : CollatzResearch.WordTrace tailWord_4871537 prefixEnd_4871537 2501440007162011822783715 := by
  unfold tailWord_4871537
  simp only [CollatzResearch.WordTrace]
  refine ⟨177679551352260916126420865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118453034234840610750947243 177679551352260916126420865)
  ·
    refine ⟨133259663514195687094815649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177679551352260916126420865 133259663514195687094815649)
    ·
      refine ⟨99944747635646765321111737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133259663514195687094815649 99944747635646765321111737)
      ·
        refine ⟨74958560726735073990833803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99944747635646765321111737 74958560726735073990833803)
        ·
          refine ⟨112437841090102610986250705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74958560726735073990833803 112437841090102610986250705)
          ·
            refine ⟨84328380817576958239688029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112437841090102610986250705 84328380817576958239688029)
            ·
              refine ⟨31623142806591359339883011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84328380817576958239688029 31623142806591359339883011)
              ·
                refine ⟨47434714209887039009824517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31623142806591359339883011 47434714209887039009824517)
                ·
                  refine ⟨8894008914353819814342097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47434714209887039009824517 8894008914353819814342097)
                  ·
                    refine ⟨6670506685765364860756573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8894008914353819814342097 6670506685765364860756573)
                    ·
                      refine ⟨2501440007162011822783715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670506685765364860756573 2501440007162011822783715)
                      ·
                        rfl

theorem cell23_4871537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_4871537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871537 prefixEnd_4871537 := by exact prefixLift 4871537
  have htrace : WordTrace (prefixWord ++ tailWord_4871537) baseStart_4871537 baseEnd_4871537 := by
    simpa [prefixWord, tailWord_4871537, baseEnd_4871537] using wordTrace_append hprefix tailTrace_4871537
  have hstable : (prefixWord ++ tailWord_4871537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871537).length < 2 ^ (prefixWord ++ tailWord_4871537).sum := by decide
  have hdescent : baseEnd_4871537 < baseStart_4871537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871607 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_4871607 : Nat := 118140960795 + 4871607 * 2 ^ 59
def prefixEnd_4871607 : Nat := 4983230072969 + 3 ^ 40 * 4871607 * 2
def baseEnd_4871607 : Nat := 2501475950807826548908393

theorem tailTrace_4871607 : CollatzResearch.WordTrace tailWord_4871607 prefixEnd_4871607 2501475950807826548908393 := by
  unfold tailWord_4871607
  simp only [CollatzResearch.WordTrace]
  refine ⟨177682104462007318081469075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118454736308004878720979383 177682104462007318081469075)
  ·
    refine ⟨266523156693010977122203613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177682104462007318081469075 266523156693010977122203613)
    ·
      refine ⟨99946183759879116420826355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266523156693010977122203613 99946183759879116420826355)
      ·
        refine ⟨149919275639818674631239533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99946183759879116420826355 149919275639818674631239533)
        ·
          refine ⟨56219728364932002986714825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149919275639818674631239533 56219728364932002986714825)
          ·
            refine ⟨42164796273699002240036119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56219728364932002986714825 42164796273699002240036119)
            ·
              refine ⟨63247194410548503360054179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42164796273699002240036119 63247194410548503360054179)
              ·
                refine ⟨94870791615822755040081269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63247194410548503360054179 94870791615822755040081269)
                ·
                  refine ⟨8894136713983383285007619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94870791615822755040081269 8894136713983383285007619)
                  ·
                    refine ⟨13341205070975074927511429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8894136713983383285007619 13341205070975074927511429)
                    ·
                      refine ⟨2501475950807826548908393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13341205070975074927511429 2501475950807826548908393)
                      ·
                        rfl

theorem cell23_4871607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_4871607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871607 prefixEnd_4871607 := by exact prefixLift 4871607
  have htrace : WordTrace (prefixWord ++ tailWord_4871607) baseStart_4871607 baseEnd_4871607 := by
    simpa [prefixWord, tailWord_4871607, baseEnd_4871607] using wordTrace_append hprefix tailTrace_4871607
  have hstable : (prefixWord ++ tailWord_4871607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871607).length < 2 ^ (prefixWord ++ tailWord_4871607).sum := by decide
  have hdescent : baseEnd_4871607 < baseStart_4871607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871624 : List Nat := [2, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_4871624 : Nat := 118140960795 + 4871624 * 2 ^ 59
def prefixEnd_4871624 : Nat := 4983230072969 + 3 ^ 40 * 4871624 * 2
def baseEnd_4871624 : Nat := 2501484679978952982395815

theorem tailTrace_4871624 : CollatzResearch.WordTrace tailWord_4871624 prefixEnd_4871624 2501484679978952982395815 := by
  unfold tailWord_4871624
  simp only [CollatzResearch.WordTrace]
  refine ⟨88841362251472864992418963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118455149668630486656558617 88841362251472864992418963)
  ·
    refine ⟨133262043377209297488628445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88841362251472864992418963 133262043377209297488628445)
    ·
      refine ⟨49973266266453486558235667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133262043377209297488628445 49973266266453486558235667)
      ·
        refine ⟨74959899399680229837353501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49973266266453486558235667 74959899399680229837353501)
        ·
          refine ⟨28109962274880086189007563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74959899399680229837353501 28109962274880086189007563)
          ·
            refine ⟨42164943412320129283511345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28109962274880086189007563 42164943412320129283511345)
            ·
              refine ⟨31623707559240096962633509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42164943412320129283511345 31623707559240096962633509)
              ·
                refine ⟨5929445167357518180493783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31623707559240096962633509 5929445167357518180493783)
                ·
                  refine ⟨8894167751036277270740675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929445167357518180493783 8894167751036277270740675)
                  ·
                    refine ⟨13341251626554415906111013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8894167751036277270740675 13341251626554415906111013)
                    ·
                      refine ⟨2501484679978952982395815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13341251626554415906111013 2501484679978952982395815)
                      ·
                        rfl

theorem cell23_4871624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_4871624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871624 prefixEnd_4871624 := by exact prefixLift 4871624
  have htrace : WordTrace (prefixWord ++ tailWord_4871624) baseStart_4871624 baseEnd_4871624 := by
    simpa [prefixWord, tailWord_4871624, baseEnd_4871624] using wordTrace_append hprefix tailTrace_4871624
  have hstable : (prefixWord ++ tailWord_4871624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871624).length < 2 ^ (prefixWord ++ tailWord_4871624).sum := by decide
  have hdescent : baseEnd_4871624 < baseStart_4871624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871628 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_4871628 : Nat := 118140960795 + 4871628 * 2 ^ 59
def prefixEnd_4871628 : Nat := 4983230072969 + 3 ^ 40 * 4871628 * 2
def baseEnd_4871628 : Nat := 2501486733901570966745797

theorem tailTrace_4871628 : CollatzResearch.WordTrace tailWord_4871628 prefixEnd_4871628 2501486733901570966745797 := by
  unfold tailWord_4871628
  simp only [CollatzResearch.WordTrace]
  refine ⟨88841435197465619333991769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118455246929954159111989025 88841435197465619333991769)
  ·
    refine ⟨66631076398099214500493827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88841435197465619333991769 66631076398099214500493827)
    ·
      refine ⟨99946614597148821750740741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66631076398099214500493827 99946614597148821750740741)
      ·
        refine ⟨18739990236965404078263889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99946614597148821750740741 18739990236965404078263889)
        ·
          refine ⟨14054992677724053058697917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18739990236965404078263889 14054992677724053058697917)
          ·
            refine ⟨5270622254146519897011719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14054992677724053058697917 5270622254146519897011719)
            ·
              refine ⟨7905933381219779845517579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270622254146519897011719 7905933381219779845517579)
              ·
                refine ⟨11858900071829669768276369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7905933381219779845517579 11858900071829669768276369)
                ·
                  refine ⟨8894175053872252326207277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11858900071829669768276369 8894175053872252326207277)
                  ·
                    refine ⟨3335315645202094622327729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8894175053872252326207277 3335315645202094622327729)
                    ·
                      refine ⟨2501486733901570966745797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335315645202094622327729 2501486733901570966745797)
                      ·
                        rfl

theorem cell23_4871628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_4871628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871628 prefixEnd_4871628 := by exact prefixLift 4871628
  have htrace : WordTrace (prefixWord ++ tailWord_4871628) baseStart_4871628 baseEnd_4871628 := by
    simpa [prefixWord, tailWord_4871628, baseEnd_4871628] using wordTrace_append hprefix tailTrace_4871628
  have hstable : (prefixWord ++ tailWord_4871628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871628).length < 2 ^ (prefixWord ++ tailWord_4871628).sum := by decide
  have hdescent : baseEnd_4871628 < baseStart_4871628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871638 : List Nat := [5, 2, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4871638 : Nat := 118140960795 + 4871638 * 2 ^ 59
def prefixEnd_4871638 : Nat := 4983230072969 + 3 ^ 40 * 4871638 * 2
def baseEnd_4871638 : Nat := 833830622902705309206917

theorem tailTrace_4871638 : CollatzResearch.WordTrace tailWord_4871638 prefixEnd_4871638 833830622902705309206917 := by
  unfold tailWord_4871638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11105202195305938148490473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118455490083263340250565045 11105202195305938148490473)
  ·
    refine ⟨8328901646479453611367855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11105202195305938148490473 8328901646479453611367855)
    ·
      refine ⟨12493352469719180417051783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8328901646479453611367855 12493352469719180417051783)
      ·
        refine ⟨18740028704578770625577675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12493352469719180417051783 18740028704578770625577675)
        ·
          refine ⟨28110043056868155938366513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18740028704578770625577675 28110043056868155938366513)
          ·
            refine ⟨21082532292651116953774885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28110043056868155938366513 21082532292651116953774885)
            ·
              refine ⟨3952974804872084428832791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21082532292651116953774885 3952974804872084428832791)
              ·
                refine ⟨5929462207308126643249187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952974804872084428832791 5929462207308126643249187)
                ·
                  refine ⟨8894193310962189964873781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929462207308126643249187 8894193310962189964873781)
                  ·
                    refine ⟨833830622902705309206917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8894193310962189964873781 833830622902705309206917)
                    ·
                      rfl

theorem cell23_4871638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4871638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871638 prefixEnd_4871638 := by exact prefixLift 4871638
  have htrace : WordTrace (prefixWord ++ tailWord_4871638) baseStart_4871638 baseEnd_4871638 := by
    simpa [prefixWord, tailWord_4871638, baseEnd_4871638] using wordTrace_append hprefix tailTrace_4871638
  have hstable : (prefixWord ++ tailWord_4871638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871638).length < 2 ^ (prefixWord ++ tailWord_4871638).sum := by decide
  have hdescent : baseEnd_4871638 < baseStart_4871638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871641 : List Nat := [1, 2, 1, 2, 4, 2, 4, 1, 1, 1, 4]
def baseStart_4871641 : Nat := 118140960795 + 4871641 * 2 ^ 59
def prefixEnd_4871641 : Nat := 4983230072969 + 3 ^ 40 * 4871641 * 2
def baseEnd_4871641 : Nat := 2501493409150079415883237

theorem tailTrace_4871641 : CollatzResearch.WordTrace tailWord_4871641 prefixEnd_4871641 2501493409150079415883237 := by
  unfold tailWord_4871641
  simp only [CollatzResearch.WordTrace]
  refine ⟨177683344543884141888206777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118455563029256094592137851 177683344543884141888206777)
  ·
    refine ⟨133262508407913106416155083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177683344543884141888206777 133262508407913106416155083)
    ·
      refine ⟨199893762611869659624232625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133262508407913106416155083 199893762611869659624232625)
      ·
        refine ⟨149920321958902244718174469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199893762611869659624232625 149920321958902244718174469)
        ·
          refine ⟨28110060367294170884657713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149920321958902244718174469 28110060367294170884657713)
          ·
            refine ⟨21082545275470628163493285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28110060367294170884657713 21082545275470628163493285)
            ·
              refine ⟨3952977239150742780654991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21082545275470628163493285 3952977239150742780654991)
              ·
                refine ⟨5929465858726114170982487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3952977239150742780654991 5929465858726114170982487)
                ·
                  refine ⟨8894198788089171256473731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929465858726114170982487 8894198788089171256473731)
                  ·
                    refine ⟨13341298182133756884710597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8894198788089171256473731 13341298182133756884710597)
                    ·
                      refine ⟨2501493409150079415883237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13341298182133756884710597 2501493409150079415883237)
                      ·
                        rfl

theorem cell23_4871641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 1, 1, 4].length) (baseStart_4871641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871641 prefixEnd_4871641 := by exact prefixLift 4871641
  have htrace : WordTrace (prefixWord ++ tailWord_4871641) baseStart_4871641 baseEnd_4871641 := by
    simpa [prefixWord, tailWord_4871641, baseEnd_4871641] using wordTrace_append hprefix tailTrace_4871641
  have hstable : (prefixWord ++ tailWord_4871641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871641).length < 2 ^ (prefixWord ++ tailWord_4871641).sum := by decide
  have hdescent : baseEnd_4871641 < baseStart_4871641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871651 : List Nat := [1, 1, 1, 6, 2, 1, 3, 2, 2, 4]
def baseStart_4871651 : Nat := 118140960795 + 4871651 * 2 ^ 59
def prefixEnd_4871651 : Nat := 4983230072969 + 3 ^ 40 * 4871651 * 2
def baseEnd_4871651 : Nat := 833832847985541458919397

theorem tailTrace_4871651 : CollatzResearch.WordTrace tailWord_4871651 prefixEnd_4871651 833832847985541458919397 := by
  unfold tailWord_4871651
  simp only [CollatzResearch.WordTrace]
  refine ⟨177683709273847913596070807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118455806182565275730713871 177683709273847913596070807)
  ·
    refine ⟨266525563910771870394106211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177683709273847913596070807 266525563910771870394106211)
    ·
      refine ⟨399788345866157805591159317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266525563910771870394106211 399788345866157805591159317)
      ·
        refine ⟨18740078712476147137085593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 399788345866157805591159317 18740078712476147137085593)
        ·
          refine ⟨14055059034357110352814195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18740078712476147137085593 14055059034357110352814195)
          ·
            refine ⟨21082588551535665529221293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14055059034357110352814195 21082588551535665529221293)
            ·
              refine ⟨7905970706825874573457985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21082588551535665529221293 7905970706825874573457985)
              ·
                refine ⟨5929478030119405930093489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7905970706825874573457985 5929478030119405930093489)
                ·
                  refine ⟨4447108522589554447570117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5929478030119405930093489 4447108522589554447570117)
                  ·
                    refine ⟨833832847985541458919397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447108522589554447570117 833832847985541458919397)
                    ·
                      rfl

theorem cell23_4871651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 2, 4].length) (baseStart_4871651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871651 prefixEnd_4871651 := by exact prefixLift 4871651
  have htrace : WordTrace (prefixWord ++ tailWord_4871651) baseStart_4871651 baseEnd_4871651 := by
    simpa [prefixWord, tailWord_4871651, baseEnd_4871651] using wordTrace_append hprefix tailTrace_4871651
  have hstable : (prefixWord ++ tailWord_4871651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871651).length < 2 ^ (prefixWord ++ tailWord_4871651).sum := by decide
  have hdescent : baseEnd_4871651 < baseStart_4871651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871661 : List Nat := [1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_4871661 : Nat := 118140960795 + 4871661 * 2 ^ 59
def prefixEnd_4871661 : Nat := 4983230072969 + 3 ^ 40 * 4871661 * 2
def baseEnd_4871661 : Nat := 2501503678763169337633145

theorem tailTrace_4871661 : CollatzResearch.WordTrace tailWord_4871661 prefixEnd_4871661 2501503678763169337633145 := by
  unfold tailWord_4871661
  simp only [CollatzResearch.WordTrace]
  refine ⟨177684074003811685303934837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118456049335874456869289891 177684074003811685303934837)
  ·
    refine ⟨16657881937857345497243891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177684074003811685303934837 16657881937857345497243891)
    ·
      refine ⟨24986822906786018245865837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16657881937857345497243891 24986822906786018245865837)
      ·
        refine ⟨9370058590044756842199689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24986822906786018245865837 9370058590044756842199689)
        ·
          refine ⟨7027543942533567631649767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370058590044756842199689 7027543942533567631649767)
          ·
            refine ⟨10541315913800351447474651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7027543942533567631649767 10541315913800351447474651)
            ·
              refine ⟨15811973870700527171211977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10541315913800351447474651 15811973870700527171211977)
              ·
                refine ⟨11858980403025395378408983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15811973870700527171211977 11858980403025395378408983)
                ·
                  refine ⟨17788470604538093067613475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11858980403025395378408983 17788470604538093067613475)
                  ·
                    refine ⟨26682705906807139601420213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17788470604538093067613475 26682705906807139601420213)
                    ·
                      refine ⟨2501503678763169337633145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26682705906807139601420213 2501503678763169337633145)
                      ·
                        rfl

theorem cell23_4871661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_4871661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871661 prefixEnd_4871661 := by exact prefixLift 4871661
  have htrace : WordTrace (prefixWord ++ tailWord_4871661) baseStart_4871661 baseEnd_4871661 := by
    simpa [prefixWord, tailWord_4871661, baseEnd_4871661] using wordTrace_append hprefix tailTrace_4871661
  have hstable : (prefixWord ++ tailWord_4871661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871661).length < 2 ^ (prefixWord ++ tailWord_4871661).sum := by decide
  have hdescent : baseEnd_4871661 < baseStart_4871661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871681 : List Nat := [1, 2, 4, 1, 4, 2, 2, 7]
def baseStart_4871681 : Nat := 118140960795 + 4871681 * 2 ^ 59
def prefixEnd_4871681 : Nat := 4983230072969 + 3 ^ 40 * 4871681 * 2
def baseEnd_4871681 : Nat := 92648664754676268866039

theorem tailTrace_4871681 : CollatzResearch.WordTrace tailWord_4871681 prefixEnd_4871681 92648664754676268866039 := by
  unfold tailWord_4871681
  simp only [CollatzResearch.WordTrace]
  refine ⟨177684803463739228719662897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118456535642492819146441931 177684803463739228719662897)
  ·
    refine ⟨133263602597804421539747173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177684803463739228719662897 133263602597804421539747173)
    ·
      refine ⟨24986925487088329038702595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133263602597804421539747173 24986925487088329038702595)
      ·
        refine ⟨37480388230632493558053893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24986925487088329038702595 37480388230632493558053893)
        ·
          refine ⟨7027572793243592542135105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37480388230632493558053893 7027572793243592542135105)
          ·
            refine ⟨5270679594932694406601329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027572793243592542135105 5270679594932694406601329)
            ·
              refine ⟨3953009696199520804950997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5270679594932694406601329 3953009696199520804950997)
              ·
                refine ⟨92648664754676268866039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3953009696199520804950997 92648664754676268866039)
                ·
                  rfl

theorem cell23_4871681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 2, 7].length) (baseStart_4871681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871681 prefixEnd_4871681 := by exact prefixLift 4871681
  have htrace : WordTrace (prefixWord ++ tailWord_4871681) baseStart_4871681 baseEnd_4871681 := by
    simpa [prefixWord, tailWord_4871681, baseEnd_4871681] using wordTrace_append hprefix tailTrace_4871681
  have hstable : (prefixWord ++ tailWord_4871681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871681).length < 2 ^ (prefixWord ++ tailWord_4871681).sum := by decide
  have hdescent : baseEnd_4871681 < baseStart_4871681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871686 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4871686 : Nat := 118140960795 + 4871686 * 2 ^ 59
def prefixEnd_4871686 : Nat := 4983230072969 + 3 ^ 40 * 4871686 * 2
def baseEnd_4871686 : Nat := 2501516515779531739820531

theorem tailTrace_4871686 : CollatzResearch.WordTrace tailWord_4871686 prefixEnd_4871686 2501516515779531739820531 := by
  unfold tailWord_4871686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552655807147534830424841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118456657219147409715729941 5552655807147534830424841)
  ·
    refine ⟨4164491855360651122818631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5552655807147534830424841 4164491855360651122818631)
    ·
      refine ⟨6246737783040976684227947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164491855360651122818631 6246737783040976684227947)
      ·
        refine ⟨9370106674561465026341921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6246737783040976684227947 9370106674561465026341921)
        ·
          refine ⟨7027580005921098769756441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370106674561465026341921 7027580005921098769756441)
          ·
            refine ⟨5270685004440824077317331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027580005921098769756441 5270685004440824077317331)
            ·
              refine ⟨7906027506661236115975997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270685004440824077317331 7906027506661236115975997)
              ·
                refine ⟨2964760314997963543490999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7906027506661236115975997 2964760314997963543490999)
                ·
                  refine ⟨4447140472496945315236499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964760314997963543490999 4447140472496945315236499)
                  ·
                    refine ⟨6670710708745417972854749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447140472496945315236499 6670710708745417972854749)
                    ·
                      refine ⟨2501516515779531739820531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670710708745417972854749 2501516515779531739820531)
                      ·
                        rfl

theorem cell23_4871686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4871686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871686 prefixEnd_4871686 := by exact prefixLift 4871686
  have htrace : WordTrace (prefixWord ++ tailWord_4871686) baseStart_4871686 baseEnd_4871686 := by
    simpa [prefixWord, tailWord_4871686, baseEnd_4871686] using wordTrace_append hprefix tailTrace_4871686
  have hstable : (prefixWord ++ tailWord_4871686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871686).length < 2 ^ (prefixWord ++ tailWord_4871686).sum := by decide
  have hdescent : baseEnd_4871686 < baseStart_4871686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871692 : List Nat := [2, 2, 1, 2, 5, 2, 1, 3, 1, 2, 2]
def baseStart_4871692 : Nat := 118140960795 + 4871692 * 2 ^ 59
def prefixEnd_4871692 : Nat := 4983230072969 + 3 ^ 40 * 4871692 * 2
def baseEnd_4871692 : Nat := 2501519596663458716345503

theorem tailTrace_4871692 : CollatzResearch.WordTrace tailWord_4871692 prefixEnd_4871692 2501519596663458716345503 := by
  unfold tailWord_4871692
  simp only [CollatzResearch.WordTrace]
  refine ⟨88842602333349688799156665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118456803111132918398875553 88842602333349688799156665)
  ·
    refine ⟨66631951750012266599367499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88842602333349688799156665 66631951750012266599367499)
    ·
      refine ⟨99947927625018399899051249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66631951750012266599367499 99947927625018399899051249)
      ·
        refine ⟨74960945718763799924288437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99947927625018399899051249 74960945718763799924288437)
        ·
          refine ⟨7027588661134106242902041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74960945718763799924288437 7027588661134106242902041)
          ·
            refine ⟨5270691495850579682176531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027588661134106242902041 5270691495850579682176531)
            ·
              refine ⟨7906037243775869523264797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270691495850579682176531 7906037243775869523264797)
              ·
                refine ⟨2964763966415951071224299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7906037243775869523264797 2964763966415951071224299)
                ·
                  refine ⟨4447145949623926606836449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964763966415951071224299 4447145949623926606836449)
                  ·
                    refine ⟨3335359462217944955127337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4447145949623926606836449 3335359462217944955127337)
                    ·
                      refine ⟨2501519596663458716345503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335359462217944955127337 2501519596663458716345503)
                      ·
                        rfl

theorem cell23_4871692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_4871692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871692 prefixEnd_4871692 := by exact prefixLift 4871692
  have htrace : WordTrace (prefixWord ++ tailWord_4871692) baseStart_4871692 baseEnd_4871692 := by
    simpa [prefixWord, tailWord_4871692, baseEnd_4871692] using wordTrace_append hprefix tailTrace_4871692
  have hstable : (prefixWord ++ tailWord_4871692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871692).length < 2 ^ (prefixWord ++ tailWord_4871692).sum := by decide
  have hdescent : baseEnd_4871692 < baseStart_4871692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871717 : List Nat := [1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_4871717 : Nat := 118140960795 + 4871717 * 2 ^ 59
def prefixEnd_4871717 : Nat := 4983230072969 + 3 ^ 40 * 4871717 * 2
def baseEnd_4871717 : Nat := 2501532433679821118532887

theorem tailTrace_4871717 : CollatzResearch.WordTrace tailWord_4871717 prefixEnd_4871717 2501532433679821118532887 := by
  unfold tailWord_4871717
  simp only [CollatzResearch.WordTrace]
  refine ⟨177686116491608806867973405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118457410994405871245315603 177686116491608806867973405)
  ·
    refine ⟨66632293684353302575490027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177686116491608806867973405 66632293684353302575490027)
    ·
      refine ⟨99948440526529953863235041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66632293684353302575490027 99948440526529953863235041)
      ·
        refine ⟨74961330394897465397426281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99948440526529953863235041 74961330394897465397426281)
        ·
          refine ⟨56220997796173099048069711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74961330394897465397426281 56220997796173099048069711)
          ·
            refine ⟨84331496694259648572104567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56220997796173099048069711 84331496694259648572104567)
            ·
              refine ⟨126497245041389472858156851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84331496694259648572104567 126497245041389472858156851)
              ·
                refine ⟨189745867562084209287235277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126497245041389472858156851 189745867562084209287235277)
                ·
                  refine ⟨71154700335781578482713229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189745867562084209287235277 71154700335781578482713229)
                  ·
                    refine ⟨26683012625918091931017461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71154700335781578482713229 26683012625918091931017461)
                    ·
                      refine ⟨2501532433679821118532887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26683012625918091931017461 2501532433679821118532887)
                      ·
                        rfl

theorem cell23_4871717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_4871717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871717 prefixEnd_4871717 := by exact prefixLift 4871717
  have htrace : WordTrace (prefixWord ++ tailWord_4871717) baseStart_4871717 baseEnd_4871717 := by
    simpa [prefixWord, tailWord_4871717, baseEnd_4871717] using wordTrace_append hprefix tailTrace_4871717
  have hstable : (prefixWord ++ tailWord_4871717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871717).length < 2 ^ (prefixWord ++ tailWord_4871717).sum := by decide
  have hdescent : baseEnd_4871717 < baseStart_4871717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871781 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_4871781 : Nat := 118140960795 + 4871781 * 2 ^ 59
def prefixEnd_4871781 : Nat := 4983230072969 + 3 ^ 40 * 4871781 * 2
def baseEnd_4871781 : Nat := 2501565296441708868132593

theorem tailTrace_4871781 : CollatzResearch.WordTrace tailWord_4871781 prefixEnd_4871781 2501565296441708868132593 := by
  unfold tailWord_4871781
  simp only [CollatzResearch.WordTrace]
  refine ⟨177688450763376945798303197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118458967175584630532202131 177688450763376945798303197)
  ·
    refine ⟨66633169036266354674363699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177688450763376945798303197 66633169036266354674363699)
    ·
      refine ⟨99949753554399532011545549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66633169036266354674363699 99949753554399532011545549)
      ·
        refine ⟨37481157582899824504329581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99949753554399532011545549 37481157582899824504329581)
        ·
          refine ⟨14055434093587434189123593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37481157582899824504329581 14055434093587434189123593)
          ·
            refine ⟨10541575570190575641842695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14055434093587434189123593 10541575570190575641842695)
            ·
              refine ⟨15812363355285863462764043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10541575570190575641842695 15812363355285863462764043)
              ·
                refine ⟨23718545032928795194146065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15812363355285863462764043 23718545032928795194146065)
                ·
                  refine ⟨17788908774696596395609549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23718545032928795194146065 17788908774696596395609549)
                  ·
                    refine ⟨6670840790511223648353581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17788908774696596395609549 6670840790511223648353581)
                    ·
                      refine ⟨2501565296441708868132593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670840790511223648353581 2501565296441708868132593)
                      ·
                        rfl

theorem cell23_4871781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_4871781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871781 prefixEnd_4871781 := by exact prefixLift 4871781
  have htrace : WordTrace (prefixWord ++ tailWord_4871781) baseStart_4871781 baseEnd_4871781 := by
    simpa [prefixWord, tailWord_4871781, baseEnd_4871781] using wordTrace_append hprefix tailTrace_4871781
  have hstable : (prefixWord ++ tailWord_4871781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871781).length < 2 ^ (prefixWord ++ tailWord_4871781).sum := by decide
  have hdescent : baseEnd_4871781 < baseStart_4871781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871831 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 3, 4]
def baseStart_4871831 : Nat := 118140960795 + 4871831 * 2 ^ 59
def prefixEnd_4871831 : Nat := 4983230072969 + 3 ^ 40 * 4871831 * 2
def baseEnd_4871831 : Nat := 833863656824811224169121

theorem tailTrace_4871831 : CollatzResearch.WordTrace tailWord_4871831 prefixEnd_4871831 833863656824811224169121 := by
  unfold tailWord_4871831
  simp only [CollatzResearch.WordTrace]
  refine ⟨177690274413195804337623347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118460182942130536225082231 177690274413195804337623347)
  ·
    refine ⟨266535411619793706506435021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177690274413195804337623347 266535411619793706506435021)
    ·
      refine ⟨99950779357422639939913133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266535411619793706506435021 99950779357422639939913133)
      ·
        refine ⟨37481542259033489977467425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99950779357422639939913133 37481542259033489977467425)
        ·
          refine ⟨28111156694275117483100569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37481542259033489977467425 28111156694275117483100569)
          ·
            refine ⟨21083367520706338112325427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28111156694275117483100569 21083367520706338112325427)
            ·
              refine ⟨31625051281059507168488141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21083367520706338112325427 31625051281059507168488141)
              ·
                refine ⟨11859394230397315188183053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31625051281059507168488141 11859394230397315188183053)
                ·
                  refine ⟨4447272836398993195568645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11859394230397315188183053 4447272836398993195568645)
                  ·
                    refine ⟨833863656824811224169121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447272836398993195568645 833863656824811224169121)
                    ·
                      rfl

theorem cell23_4871831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_4871831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871831 prefixEnd_4871831 := by exact prefixLift 4871831
  have htrace : WordTrace (prefixWord ++ tailWord_4871831) baseStart_4871831 baseEnd_4871831 := by
    simpa [prefixWord, tailWord_4871831, baseEnd_4871831] using wordTrace_append hprefix tailTrace_4871831
  have hstable : (prefixWord ++ tailWord_4871831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871831).length < 2 ^ (prefixWord ++ tailWord_4871831).sum := by decide
  have hdescent : baseEnd_4871831 < baseStart_4871831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871841 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 3]
def baseStart_4871841 : Nat := 118140960795 + 4871841 * 2 ^ 59
def prefixEnd_4871841 : Nat := 4983230072969 + 3 ^ 40 * 4871841 * 2
def baseEnd_4871841 : Nat := 2501596105280978633382317

theorem tailTrace_4871841 : CollatzResearch.WordTrace tailWord_4871841 prefixEnd_4871841 2501596105280978633382317 := by
  unfold tailWord_4871841
  simp only [CollatzResearch.WordTrace]
  refine ⟨177690639143159576045487377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118460426095439717363658251 177690639143159576045487377)
  ·
    refine ⟨133267979357369682034115533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177690639143159576045487377 133267979357369682034115533)
    ·
      refine ⟨49975492259013630762793325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133267979357369682034115533 49975492259013630762793325)
      ·
        refine ⟨18740809597130111536047497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49975492259013630762793325 18740809597130111536047497)
        ·
          refine ⟨14055607197847583652035623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18740809597130111536047497 14055607197847583652035623)
          ·
            refine ⟨21083410796771375478053435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14055607197847583652035623 21083410796771375478053435)
            ·
              refine ⟨31625116195157063217080153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21083410796771375478053435 31625116195157063217080153)
              ·
                refine ⟨23718837146367797412810115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31625116195157063217080153 23718837146367797412810115)
                ·
                  refine ⟨35578255719551696119215173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23718837146367797412810115 35578255719551696119215173)
                  ·
                    refine ⟨6670922947415943022352845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35578255719551696119215173 6670922947415943022352845)
                    ·
                      refine ⟨2501596105280978633382317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6670922947415943022352845 2501596105280978633382317)
                      ·
                        rfl

theorem cell23_4871841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_4871841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871841 prefixEnd_4871841 := by exact prefixLift 4871841
  have htrace : WordTrace (prefixWord ++ tailWord_4871841) baseStart_4871841 baseEnd_4871841 := by
    simpa [prefixWord, tailWord_4871841, baseEnd_4871841] using wordTrace_append hprefix tailTrace_4871841
  have hstable : (prefixWord ++ tailWord_4871841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871841).length < 2 ^ (prefixWord ++ tailWord_4871841).sum := by decide
  have hdescent : baseEnd_4871841 < baseStart_4871841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871882 : List Nat := [3, 1, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_4871882 : Nat := 118140960795 + 4871882 * 2 ^ 59
def prefixEnd_4871882 : Nat := 4983230072969 + 3 ^ 40 * 4871882 * 2
def baseEnd_4871882 : Nat := 833872385995937657656543

theorem tailTrace_4871882 : CollatzResearch.WordTrace tailWord_4871882 prefixEnd_4871882 833872385995937657656543 := by
  unfold tailWord_4871882
  simp only [CollatzResearch.WordTrace]
  refine ⟨44423033634002760011932475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118461423024007360031819933 44423033634002760011932475)
  ·
    refine ⟨66634550451004140017898713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44423033634002760011932475 66634550451004140017898713)
    ·
      refine ⟨49975912838253105013424035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66634550451004140017898713 49975912838253105013424035)
      ·
        refine ⟨74963869257379657520136053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49975912838253105013424035 74963869257379657520136053)
        ·
          refine ⟨7027862742879342892512755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74963869257379657520136053 7027862742879342892512755)
          ·
            refine ⟨10541794114319014338769133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7027862742879342892512755 10541794114319014338769133)
            ·
              refine ⟨3953172792869630377038425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10541794114319014338769133 3953172792869630377038425)
              ·
                refine ⟨2964879594652222782778819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953172792869630377038425 2964879594652222782778819)
                ·
                  refine ⟨4447319391978334174168229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2964879594652222782778819 4447319391978334174168229)
                  ·
                    refine ⟨833872385995937657656543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447319391978334174168229 833872385995937657656543)
                    ·
                      rfl

theorem cell23_4871882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_4871882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871882 prefixEnd_4871882 := by exact prefixLift 4871882
  have htrace : WordTrace (prefixWord ++ tailWord_4871882) baseStart_4871882 baseEnd_4871882 := by
    simpa [prefixWord, tailWord_4871882, baseEnd_4871882] using wordTrace_append hprefix tailTrace_4871882
  have hstable : (prefixWord ++ tailWord_4871882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871882).length < 2 ^ (prefixWord ++ tailWord_4871882).sum := by decide
  have hdescent : baseEnd_4871882 < baseStart_4871882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871921 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 1, 6]
def baseStart_4871921 : Nat := 118140960795 + 4871921 * 2 ^ 59
def prefixEnd_4871921 : Nat := 4983230072969 + 3 ^ 40 * 4871921 * 2
def baseEnd_4871921 : Nat := 833879061244446106793983

theorem tailTrace_4871921 : CollatzResearch.WordTrace tailWord_4871921 prefixEnd_4871921 833879061244446106793983 := by
  unfold tailWord_4871921
  simp only [CollatzResearch.WordTrace]
  refine ⟨177693556982869749708399617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118462371321913166472266411 177693556982869749708399617)
  ·
    refine ⟨133270167737152312281299713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177693556982869749708399617 133270167737152312281299713)
    ·
      refine ⟨99952625802864234210974785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133270167737152312281299713 99952625802864234210974785)
      ·
        refine ⟨74964469352148175658231089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99952625802864234210974785 74964469352148175658231089)
        ·
          refine ⟨56223352014111131743673317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74964469352148175658231089 56223352014111131743673317)
          ·
            refine ⟨10541878502645837201938747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56223352014111131743673317 10541878502645837201938747)
            ·
              refine ⟨15812817753968755802908121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10541878502645837201938747 15812817753968755802908121)
              ·
                refine ⟨11859613315476566852181091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15812817753968755802908121 11859613315476566852181091)
                ·
                  refine ⟨17789419973214850278271637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11859613315476566852181091 17789419973214850278271637)
                  ·
                    refine ⟨833879061244446106793983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17789419973214850278271637 833879061244446106793983)
                    ·
                      rfl

theorem cell23_4871921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 1, 6].length) (baseStart_4871921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871921 prefixEnd_4871921 := by exact prefixLift 4871921
  have htrace : WordTrace (prefixWord ++ tailWord_4871921) baseStart_4871921 baseEnd_4871921 := by
    simpa [prefixWord, tailWord_4871921, baseEnd_4871921] using wordTrace_append hprefix tailTrace_4871921
  have hstable : (prefixWord ++ tailWord_4871921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871921).length < 2 ^ (prefixWord ++ tailWord_4871921).sum := by decide
  have hdescent : baseEnd_4871921 < baseStart_4871921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871928 : List Nat := [2, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2]
def baseStart_4871928 : Nat := 118140960795 + 4871928 * 2 ^ 59
def prefixEnd_4871928 : Nat := 4983230072969 + 3 ^ 40 * 4871928 * 2
def baseEnd_4871928 : Nat := 2501640778097919792994417

theorem tailTrace_4871928 : CollatzResearch.WordTrace tailWord_4871928 prefixEnd_4871928 2501640778097919792994417 := by
  unfold tailWord_4871928
  simp only [CollatzResearch.WordTrace]
  refine ⟨88846906146922194951952219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118462541529229593269269625 88846906146922194951952219)
  ·
    refine ⟨133270359220383292427928329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88846906146922194951952219 133270359220383292427928329)
    ·
      refine ⟨99952769415287469320946247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133270359220383292427928329 99952769415287469320946247)
      ·
        refine ⟨149929154122931203981419371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99952769415287469320946247 149929154122931203981419371)
        ·
          refine ⟨224893731184396805972129057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149929154122931203981419371 224893731184396805972129057)
          ·
            refine ⟨168670298388297604479096793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224893731184396805972129057 168670298388297604479096793)
            ·
              refine ⟨126502723791223203359322595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168670298388297604479096793 126502723791223203359322595)
              ·
                refine ⟨189754085686834805038983893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126502723791223203359322595 189754085686834805038983893)
                ·
                  refine ⟨4447361383285190743101185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 189754085686834805038983893 4447361383285190743101185)
                  ·
                    refine ⟨3335521037463893057325889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4447361383285190743101185 3335521037463893057325889)
                    ·
                      refine ⟨2501640778097919792994417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335521037463893057325889 2501640778097919792994417)
                      ·
                        rfl

theorem cell23_4871928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 1, 7, 2, 2].length) (baseStart_4871928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871928 prefixEnd_4871928 := by exact prefixLift 4871928
  have htrace : WordTrace (prefixWord ++ tailWord_4871928) baseStart_4871928 baseEnd_4871928 := by
    simpa [prefixWord, tailWord_4871928, baseEnd_4871928] using wordTrace_append hprefix tailTrace_4871928
  have hstable : (prefixWord ++ tailWord_4871928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871928).length < 2 ^ (prefixWord ++ tailWord_4871928).sum := by decide
  have hdescent : baseEnd_4871928 < baseStart_4871928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871966 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4871966 : Nat := 118140960795 + 4871966 * 2 ^ 59
def prefixEnd_4871966 : Nat := 4983230072969 + 3 ^ 40 * 4871966 * 2
def baseEnd_4871966 : Nat := 2501660290362790644319243

theorem tailTrace_4871966 : CollatzResearch.WordTrace tailWord_4871966 prefixEnd_4871966 2501660290362790644319243 := by
  unfold tailWord_4871966
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211899783463340299223469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118463465511804481595858501 22211899783463340299223469)
  ·
    refine ⟨8329462418798752612208801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22211899783463340299223469 8329462418798752612208801)
    ·
      refine ⟨6247096814099064459156601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8329462418798752612208801 6247096814099064459156601)
      ·
        refine ⟨4685322610574298344367451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6247096814099064459156601 4685322610574298344367451)
        ·
          refine ⟨7027983915861447516551177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685322610574298344367451 7027983915861447516551177)
          ·
            refine ⟨5270987936896085637413383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7027983915861447516551177 5270987936896085637413383)
            ·
              refine ⟨7906481905344128456120075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5270987936896085637413383 7906481905344128456120075)
              ·
                refine ⟨11859722858016192684180113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906481905344128456120075 11859722858016192684180113)
                ·
                  refine ⟨8894792143512144513135085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11859722858016192684180113 8894792143512144513135085)
                  ·
                    refine ⟨3335547053817054192425657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8894792143512144513135085 3335547053817054192425657)
                    ·
                      refine ⟨2501660290362790644319243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335547053817054192425657 2501660290362790644319243)
                      ·
                        rfl

theorem cell23_4871966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4871966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871966 prefixEnd_4871966 := by exact prefixLift 4871966
  have htrace : WordTrace (prefixWord ++ tailWord_4871966) baseStart_4871966 baseEnd_4871966 := by
    simpa [prefixWord, tailWord_4871966, baseEnd_4871966] using wordTrace_append hprefix tailTrace_4871966
  have hstable : (prefixWord ++ tailWord_4871966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871966).length < 2 ^ (prefixWord ++ tailWord_4871966).sum := by decide
  have hdescent : baseEnd_4871966 < baseStart_4871966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4871982 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3]
def baseStart_4871982 : Nat := 118140960795 + 4871982 * 2 ^ 59
def prefixEnd_4871982 : Nat := 4983230072969 + 3 ^ 40 * 4871982 * 2
def baseEnd_4871982 : Nat := 2501668506053262581719169

theorem tailTrace_4871982 : CollatzResearch.WordTrace tailWord_4871982 prefixEnd_4871982 2501668506053262581719169 := by
  unfold tailWord_4871982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22211972729456094640796275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118463854557099171417580133 22211972729456094640796275)
  ·
    refine ⟨33317959094184141961194413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22211972729456094640796275 33317959094184141961194413)
    ·
      refine ⟨12494234660319053235447905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33317959094184141961194413 12494234660319053235447905)
      ·
        refine ⟨9370675995239289926585929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12494234660319053235447905 9370675995239289926585929)
        ·
          refine ⟨7028006996429467444939447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370675995239289926585929 7028006996429467444939447)
          ·
            refine ⟨10542010494644201167409171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028006996429467444939447 10542010494644201167409171)
            ·
              refine ⟨15813015741966301751113757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542010494644201167409171 15813015741966301751113757)
              ·
                refine ⟨5929880903237363156667659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15813015741966301751113757 5929880903237363156667659)
                ·
                  refine ⟨8894821354856044735001489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5929880903237363156667659 8894821354856044735001489)
                  ·
                    refine ⟨6671116016142033551251117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8894821354856044735001489 6671116016142033551251117)
                    ·
                      refine ⟨2501668506053262581719169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671116016142033551251117 2501668506053262581719169)
                      ·
                        rfl

theorem cell23_4871982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_4871982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4871982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4871982 prefixEnd_4871982 := by exact prefixLift 4871982
  have htrace : WordTrace (prefixWord ++ tailWord_4871982) baseStart_4871982 baseEnd_4871982 := by
    simpa [prefixWord, tailWord_4871982, baseEnd_4871982] using wordTrace_append hprefix tailTrace_4871982
  have hstable : (prefixWord ++ tailWord_4871982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4871982).length < 2 ^ (prefixWord ++ tailWord_4871982).sum := by decide
  have hdescent : baseEnd_4871982 < baseStart_4871982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4871982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872012 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_4872012 : Nat := 118140960795 + 4872012 * 2 ^ 59
def prefixEnd_4872012 : Nat := 4983230072969 + 3 ^ 40 * 4872012 * 2
def baseEnd_4872012 : Nat := 2501683910472897464344031

theorem tailTrace_4872012 : CollatzResearch.WordTrace tailWord_4872012 prefixEnd_4872012 2501683910472897464344031 := by
  unfold tailWord_4872012
  simp only [CollatzResearch.WordTrace]
  refine ⟨88848438012770036124981145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118464584017026714833308193 88848438012770036124981145)
  ·
    refine ⟨66636328509577527093735859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88848438012770036124981145 66636328509577527093735859)
    ·
      refine ⟨99954492764366290640603789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66636328509577527093735859 99954492764366290640603789)
      ·
        refine ⟨37482934786637358990226421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99954492764366290640603789 37482934786637358990226421)
        ·
          refine ⟨3514025136247252405333727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37482934786637358990226421 3514025136247252405333727)
          ·
            refine ⟨5271037704370878608000591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514025136247252405333727 5271037704370878608000591)
            ·
              refine ⟨7906556556556317912000887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271037704370878608000591 7906556556556317912000887)
              ·
                refine ⟨11859834834834476868001331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7906556556556317912000887 11859834834834476868001331)
                ·
                  refine ⟨17789752252251715302001997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11859834834834476868001331 17789752252251715302001997)
                  ·
                    refine ⟨6671157094594393238250749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17789752252251715302001997 6671157094594393238250749)
                    ·
                      refine ⟨2501683910472897464344031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671157094594393238250749 2501683910472897464344031)
                      ·
                        rfl

theorem cell23_4872012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_4872012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872012 prefixEnd_4872012 := by exact prefixLift 4872012
  have htrace : WordTrace (prefixWord ++ tailWord_4872012) baseStart_4872012 baseEnd_4872012 := by
    simpa [prefixWord, tailWord_4872012, baseEnd_4872012] using wordTrace_append hprefix tailTrace_4872012
  have hstable : (prefixWord ++ tailWord_4872012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872012).length < 2 ^ (prefixWord ++ tailWord_4872012).sum := by decide
  have hdescent : baseEnd_4872012 < baseStart_4872012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872058 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 5]
def baseStart_4872058 : Nat := 118140960795 + 4872058 * 2 ^ 59
def prefixEnd_4872058 : Nat := 4983230072969 + 3 ^ 40 * 4872058 * 2
def baseEnd_4872058 : Nat := 277967503398111587152091

theorem tailTrace_4872058 : CollatzResearch.WordTrace tailWord_4872058 prefixEnd_4872058 277967503398111587152091 := by
  unfold tailWord_4872058
  simp only [CollatzResearch.WordTrace]
  refine ⟨44424638445843355526534207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118465702522248948070757885 44424638445843355526534207)
  ·
    refine ⟨66636957668765033289801311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44424638445843355526534207 66636957668765033289801311)
    ·
      refine ⟨99955436503147549934701967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66636957668765033289801311 99955436503147549934701967)
      ·
        refine ⟨149933154754721324902052951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99955436503147549934701967 149933154754721324902052951)
        ·
          refine ⟨224899732132081987353079427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149933154754721324902052951 224899732132081987353079427)
          ·
            refine ⟨337349598198122981029619141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224899732132081987353079427 337349598198122981029619141)
            ·
              refine ⟨63253049662148058943053589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337349598198122981029619141 63253049662148058943053589)
              ·
                refine ⟨2964986702913190262955637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63253049662148058943053589 2964986702913190262955637)
                ·
                  refine ⟨277967503398111587152091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2964986702913190262955637 277967503398111587152091)
                  ·
                    rfl

theorem cell23_4872058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_4872058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872058 prefixEnd_4872058 := by exact prefixLift 4872058
  have htrace : WordTrace (prefixWord ++ tailWord_4872058) baseStart_4872058 baseEnd_4872058 := by
    simpa [prefixWord, tailWord_4872058, baseEnd_4872058] using wordTrace_append hprefix tailTrace_4872058
  have hstable : (prefixWord ++ tailWord_4872058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872058).length < 2 ^ (prefixWord ++ tailWord_4872058).sum := by decide
  have hdescent : baseEnd_4872058 < baseStart_4872058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872068 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_4872068 : Nat := 118140960795 + 4872068 * 2 ^ 59
def prefixEnd_4872068 : Nat := 4983230072969 + 3 ^ 40 * 4872068 * 2
def baseEnd_4872068 : Nat := 2501712665389549245243773

theorem tailTrace_4872068 : CollatzResearch.WordTrace tailWord_4872068 prefixEnd_4872068 2501712665389549245243773 := by
  unfold tailWord_4872068
  simp only [CollatzResearch.WordTrace]
  refine ⟨88849459256668596907000429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118465945675558129209333905 88849459256668596907000429)
  ·
    refine ⟨33318547221250723840125161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88849459256668596907000429 33318547221250723840125161)
    ·
      refine ⟨24988910415938042880093871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33318547221250723840125161 24988910415938042880093871)
      ·
        refine ⟨37483365623907064320140807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24988910415938042880093871 37483365623907064320140807)
        ·
          refine ⟨56225048435860596480211211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37483365623907064320140807 56225048435860596480211211)
          ·
            refine ⟨84337572653790894720316817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56225048435860596480211211 84337572653790894720316817)
            ·
              refine ⟨63253179490343171040237613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84337572653790894720316817 63253179490343171040237613)
              ·
                refine ⟨23719942308878689140089105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63253179490343171040237613 23719942308878689140089105)
                ·
                  refine ⟨17789956731659016855066829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23719942308878689140089105 17789956731659016855066829)
                  ·
                    refine ⟨6671233774372131320650061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17789956731659016855066829 6671233774372131320650061)
                    ·
                      refine ⟨2501712665389549245243773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671233774372131320650061 2501712665389549245243773)
                      ·
                        rfl

theorem cell23_4872068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_4872068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872068 prefixEnd_4872068 := by exact prefixLift 4872068
  have htrace : WordTrace (prefixWord ++ tailWord_4872068) baseStart_4872068 baseEnd_4872068 := by
    simpa [prefixWord, tailWord_4872068, baseEnd_4872068] using wordTrace_append hprefix tailTrace_4872068
  have hstable : (prefixWord ++ tailWord_4872068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872068).length < 2 ^ (prefixWord ++ tailWord_4872068).sum := by decide
  have hdescent : baseEnd_4872068 < baseStart_4872068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872086 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4872086 : Nat := 118140960795 + 4872086 * 2 ^ 59
def prefixEnd_4872086 : Nat := 4983230072969 + 3 ^ 40 * 4872086 * 2
def baseEnd_4872086 : Nat := 2501721908041330174818691

theorem tailTrace_4872086 : CollatzResearch.WordTrace tailWord_4872086 prefixEnd_4872086 2501721908041330174818691 := by
  unfold tailWord_4872086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106223439204498930509757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118466383351514655258770741 11106223439204498930509757)
  ·
    refine ⟨4164833789701687098941159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11106223439204498930509757 4164833789701687098941159)
    ·
      refine ⟨6247250684552530648411739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4164833789701687098941159 6247250684552530648411739)
      ·
        refine ⟨9370876026828795972617609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6247250684552530648411739 9370876026828795972617609)
        ·
          refine ⟨7028157020121596979463207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9370876026828795972617609 7028157020121596979463207)
          ·
            refine ⟨10542235530182395469194811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028157020121596979463207 10542235530182395469194811)
            ·
              refine ⟨15813353295273593203792217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542235530182395469194811 15813353295273593203792217)
              ·
                refine ⟨11860014971455194902844163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15813353295273593203792217 11860014971455194902844163)
                ·
                  refine ⟨17790022457182792354266245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11860014971455194902844163 17790022457182792354266245)
                  ·
                    refine ⟨3335629210721773566424921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17790022457182792354266245 3335629210721773566424921)
                    ·
                      refine ⟨2501721908041330174818691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335629210721773566424921 2501721908041330174818691)
                      ·
                        rfl

theorem cell23_4872086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4872086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872086 prefixEnd_4872086 := by exact prefixLift 4872086
  have htrace : WordTrace (prefixWord ++ tailWord_4872086) baseStart_4872086 baseEnd_4872086 := by
    simpa [prefixWord, tailWord_4872086, baseEnd_4872086] using wordTrace_append hprefix tailTrace_4872086
  have hstable : (prefixWord ++ tailWord_4872086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872086).length < 2 ^ (prefixWord ++ tailWord_4872086).sum := by decide
  have hdescent : baseEnd_4872086 < baseStart_4872086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872111 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5]
def baseStart_4872111 : Nat := 118140960795 + 4872111 * 2 ^ 59
def prefixEnd_4872111 : Nat := 4983230072969 + 3 ^ 40 * 4872111 * 2
def baseEnd_4872111 : Nat := 2501734745057692577006075

theorem tailTrace_4872111 : CollatzResearch.WordTrace tailWord_4872111 prefixEnd_4872111 2501734745057692577006075 := by
  unfold tailWord_4872111
  simp only [CollatzResearch.WordTrace]
  refine ⟨177700486852181412157816187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118466991234787608105210791 177700486852181412157816187)
  ·
    refine ⟨266550730278272118236724281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177700486852181412157816187 266550730278272118236724281)
    ·
      refine ⟨199913047708704088677543211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266550730278272118236724281 199913047708704088677543211)
      ·
        refine ⟨299869571563056133016314817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199913047708704088677543211 299869571563056133016314817)
        ·
          refine ⟨224902178672292099762236113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299869571563056133016314817 224902178672292099762236113)
          ·
            refine ⟨168676634004219074821677085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224902178672292099762236113 168676634004219074821677085)
            ·
              refine ⟨63253737751582153058128907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168676634004219074821677085 63253737751582153058128907)
              ·
                refine ⟨94880606627373229587193361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63253737751582153058128907 94880606627373229587193361)
                ·
                  refine ⟨71160454970529922190395021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94880606627373229587193361 71160454970529922190395021)
                  ·
                    refine ⟨26685170613948720821398133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71160454970529922190395021 26685170613948720821398133)
                    ·
                      refine ⟨2501734745057692577006075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26685170613948720821398133 2501734745057692577006075)
                      ·
                        rfl

theorem cell23_4872111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_4872111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872111 prefixEnd_4872111 := by exact prefixLift 4872111
  have htrace : WordTrace (prefixWord ++ tailWord_4872111) baseStart_4872111 baseEnd_4872111 := by
    simpa [prefixWord, tailWord_4872111, baseEnd_4872111] using wordTrace_append hprefix tailTrace_4872111
  have hstable : (prefixWord ++ tailWord_4872111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872111).length < 2 ^ (prefixWord ++ tailWord_4872111).sum := by decide
  have hdescent : baseEnd_4872111 < baseStart_4872111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872125 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 6, 2]
def baseStart_4872125 : Nat := 118140960795 + 4872125 * 2 ^ 59
def prefixEnd_4872125 : Nat := 4983230072969 + 3 ^ 40 * 4872125 * 2
def baseEnd_4872125 : Nat := 2501741933786855522231011

theorem tailTrace_4872125 : CollatzResearch.WordTrace tailWord_4872125 prefixEnd_4872125 2501741933786855522231011 := by
  unfold tailWord_4872125
  simp only [CollatzResearch.WordTrace]
  refine ⟨177700997474130692548825829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118467331649420461699217219 177700997474130692548825829)
  ·
    refine ⟨33318937026399504852904843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177700997474130692548825829 33318937026399504852904843)
    ·
      refine ⟨49978405539599257279357265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33318937026399504852904843 49978405539599257279357265)
      ·
        refine ⟨37483804154699442959517949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49978405539599257279357265 37483804154699442959517949)
        ·
          refine ⟨14056426558012291109819231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37483804154699442959517949 14056426558012291109819231)
          ·
            refine ⟨21084639837018436664728847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14056426558012291109819231 21084639837018436664728847)
            ·
              refine ⟨31626959755527654997093271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21084639837018436664728847 31626959755527654997093271)
              ·
                refine ⟨47440439633291482495639907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31626959755527654997093271 47440439633291482495639907)
                ·
                  refine ⟨71160659449937223743459861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47440439633291482495639907 71160659449937223743459861)
                  ·
                    refine ⟨3335655911715807362974681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71160659449937223743459861 3335655911715807362974681)
                    ·
                      refine ⟨2501741933786855522231011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335655911715807362974681 2501741933786855522231011)
                      ·
                        rfl

theorem cell23_4872125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_4872125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872125 prefixEnd_4872125 := by exact prefixLift 4872125
  have htrace : WordTrace (prefixWord ++ tailWord_4872125) baseStart_4872125 baseEnd_4872125 := by
    simpa [prefixWord, tailWord_4872125, baseEnd_4872125] using wordTrace_append hprefix tailTrace_4872125
  have hstable : (prefixWord ++ tailWord_4872125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872125).length < 2 ^ (prefixWord ++ tailWord_4872125).sum := by decide
  have hdescent : baseEnd_4872125 < baseStart_4872125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872128 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3]
def baseStart_4872128 : Nat := 118140960795 + 4872128 * 2 ^ 59
def prefixEnd_4872128 : Nat := 4983230072969 + 3 ^ 40 * 4872128 * 2
def baseEnd_4872128 : Nat := 2501743474228819010493497

theorem tailTrace_4872128 : CollatzResearch.WordTrace tailWord_4872128 prefixEnd_4872128 2501743474228819010493497 := by
  unfold tailWord_4872128
  simp only [CollatzResearch.WordTrace]
  refine ⟨88850553446559912030592519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118467404595413216040790025 88850553446559912030592519)
  ·
    refine ⟨133275830169839868045888779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88850553446559912030592519 133275830169839868045888779)
    ·
      refine ⟨199913745254759802068833169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133275830169839868045888779 199913745254759802068833169)
      ·
        refine ⟨149935308941069851551624877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199913745254759802068833169 149935308941069851551624877)
        ·
          refine ⟨56225740852901194331859329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149935308941069851551624877 56225740852901194331859329)
          ·
            refine ⟨42169305639675895748894497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56225740852901194331859329 42169305639675895748894497)
            ·
              refine ⟨31626979229756921811670873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42169305639675895748894497 31626979229756921811670873)
              ·
                refine ⟨23720234422317691358753155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31626979229756921811670873 23720234422317691358753155)
                ·
                  refine ⟨35580351633476537038129733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23720234422317691358753155 35580351633476537038129733)
                  ·
                    refine ⟨6671315931276850694649325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35580351633476537038129733 6671315931276850694649325)
                    ·
                      refine ⟨2501743474228819010493497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671315931276850694649325 2501743474228819010493497)
                      ·
                        rfl

theorem cell23_4872128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 3].length) (baseStart_4872128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872128 prefixEnd_4872128 := by exact prefixLift 4872128
  have htrace : WordTrace (prefixWord ++ tailWord_4872128) baseStart_4872128 baseEnd_4872128 := by
    simpa [prefixWord, tailWord_4872128, baseEnd_4872128] using wordTrace_append hprefix tailTrace_4872128
  have hstable : (prefixWord ++ tailWord_4872128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872128).length < 2 ^ (prefixWord ++ tailWord_4872128).sum := by decide
  have hdescent : baseEnd_4872128 < baseStart_4872128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872148 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 8]
def baseStart_4872148 : Nat := 118140960795 + 4872148 * 2 ^ 59
def prefixEnd_4872148 : Nat := 4983230072969 + 3 ^ 40 * 4872148 * 2
def baseEnd_4872148 : Nat := 277972638204656548027045

theorem tailTrace_4872148 : CollatzResearch.WordTrace tailWord_4872148 prefixEnd_4872148 277972638204656548027045 := by
  unfold tailWord_4872148
  simp only [CollatzResearch.WordTrace]
  refine ⟨88850918176523683738456549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118467890902031578317942065 88850918176523683738456549)
  ·
    refine ⟨16659547158098190700960603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88850918176523683738456549 16659547158098190700960603)
    ·
      refine ⟨24989320737147286051440905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659547158098190700960603 24989320737147286051440905)
      ·
        refine ⟨18741990552860464538580679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24989320737147286051440905 18741990552860464538580679)
        ·
          refine ⟨28112985829290696807871019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18741990552860464538580679 28112985829290696807871019)
          ·
            refine ⟨42169478743936045211806529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28112985829290696807871019 42169478743936045211806529)
            ·
              refine ⟨31627109057952033908854897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42169478743936045211806529 31627109057952033908854897)
              ·
                refine ⟨23720331793464025431641173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31627109057952033908854897 23720331793464025431641173)
                ·
                  refine ⟨277972638204656548027045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23720331793464025431641173 277972638204656548027045)
                  ·
                    rfl

theorem cell23_4872148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_4872148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872148 prefixEnd_4872148 := by exact prefixLift 4872148
  have htrace : WordTrace (prefixWord ++ tailWord_4872148) baseStart_4872148 baseEnd_4872148 := by
    simpa [prefixWord, tailWord_4872148, baseEnd_4872148] using wordTrace_append hprefix tailTrace_4872148
  have hstable : (prefixWord ++ tailWord_4872148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872148).length < 2 ^ (prefixWord ++ tailWord_4872148).sum := by decide
  have hdescent : baseEnd_4872148 < baseStart_4872148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872152 : List Nat := [2, 1, 2, 2, 2, 2, 4, 3, 1, 4]
def baseStart_4872152 : Nat := 118140960795 + 4872152 * 2 ^ 59
def prefixEnd_4872152 : Nat := 4983230072969 + 3 ^ 40 * 4872152 * 2
def baseEnd_4872152 : Nat := 833918599254842305531129

theorem tailTrace_4872152 : CollatzResearch.WordTrace tailWord_4872152 prefixEnd_4872152 833918599254842305531129 := by
  unfold tailWord_4872152
  simp only [CollatzResearch.WordTrace]
  refine ⟨88850991122516438080029355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118467988163355250773372473 88850991122516438080029355)
  ·
    refine ⟨133276486683774657120044033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88850991122516438080029355 133276486683774657120044033)
    ·
      refine ⟨99957365012830992840033025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133276486683774657120044033 99957365012830992840033025)
      ·
        refine ⟨74968023759623244630024769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99957365012830992840033025 74968023759623244630024769)
        ·
          refine ⟨56226017819717433472518577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74968023759623244630024769 56226017819717433472518577)
          ·
            refine ⟨42169513364788075104388933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56226017819717433472518577 42169513364788075104388933)
            ·
              refine ⟨7906783755897764082072925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42169513364788075104388933 7906783755897764082072925)
              ·
                refine ⟨2965043908461661530777347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7906783755897764082072925 2965043908461661530777347)
                ·
                  refine ⟨4447565862692492296166021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965043908461661530777347 4447565862692492296166021)
                  ·
                    refine ⟨833918599254842305531129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447565862692492296166021 833918599254842305531129)
                    ·
                      rfl

theorem cell23_4872152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 1, 4].length) (baseStart_4872152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872152 prefixEnd_4872152 := by exact prefixLift 4872152
  have htrace : WordTrace (prefixWord ++ tailWord_4872152) baseStart_4872152 baseEnd_4872152 := by
    simpa [prefixWord, tailWord_4872152, baseEnd_4872152] using wordTrace_append hprefix tailTrace_4872152
  have hstable : (prefixWord ++ tailWord_4872152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872152).length < 2 ^ (prefixWord ++ tailWord_4872152).sum := by decide
  have hdescent : baseEnd_4872152 < baseStart_4872152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872185 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 1, 5, 2]
def baseStart_4872185 : Nat := 118140960795 + 4872185 * 2 ^ 59
def prefixEnd_4872185 : Nat := 4983230072969 + 3 ^ 40 * 4872185 * 2
def baseEnd_4872185 : Nat := 2501772742626125287480735

theorem tailTrace_4872185 : CollatzResearch.WordTrace tailWord_4872185 prefixEnd_4872185 2501772742626125287480735 := by
  unfold tailWord_4872185
  simp only [CollatzResearch.WordTrace]
  refine ⟨177703185853913322796010009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118468790569275548530673339 177703185853913322796010009)
  ·
    refine ⟨133277389390434992097007507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177703185853913322796010009 133277389390434992097007507)
    ·
      refine ⟨199916084085652488145511261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133277389390434992097007507 199916084085652488145511261)
      ·
        refine ⟨74968531532119683054566723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199916084085652488145511261 74968531532119683054566723)
        ·
          refine ⟨112452797298179524581850085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74968531532119683054566723 112452797298179524581850085)
          ·
            refine ⟨21084899493408660859096891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112452797298179524581850085 21084899493408660859096891)
            ·
              refine ⟨31627349240112991288645337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21084899493408660859096891 31627349240112991288645337)
              ·
                refine ⟨23720511930084743466484003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31627349240112991288645337 23720511930084743466484003)
                ·
                  refine ⟨35580767895127115199726005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23720511930084743466484003 35580767895127115199726005)
                  ·
                    refine ⟨3335696990168167049974313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35580767895127115199726005 3335696990168167049974313)
                    ·
                      refine ⟨2501772742626125287480735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335696990168167049974313 2501772742626125287480735)
                      ·
                        rfl

theorem cell23_4872185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_4872185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872185 prefixEnd_4872185 := by exact prefixLift 4872185
  have htrace : WordTrace (prefixWord ++ tailWord_4872185) baseStart_4872185 baseEnd_4872185 := by
    simpa [prefixWord, tailWord_4872185, baseEnd_4872185] using wordTrace_append hprefix tailTrace_4872185
  have hstable : (prefixWord ++ tailWord_4872185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872185).length < 2 ^ (prefixWord ++ tailWord_4872185).sum := by decide
  have hdescent : baseEnd_4872185 < baseStart_4872185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872226 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 1, 1, 3]
def baseStart_4872226 : Nat := 118140960795 + 4872226 * 2 ^ 59
def prefixEnd_4872226 : Nat := 4983230072969 + 3 ^ 40 * 4872226 * 2
def baseEnd_4872226 : Nat := 2501793795332959627068047

theorem tailTrace_4872226 : CollatzResearch.WordTrace tailWord_4872226 prefixEnd_4872226 2501793795332959627068047 := by
  unfold tailWord_4872226
  simp only [CollatzResearch.WordTrace]
  refine ⟨44426170311691196699563133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118469787497843191198835021 44426170311691196699563133)
  ·
    refine ⟨16659813866884198762336175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44426170311691196699563133 16659813866884198762336175)
    ·
      refine ⟨24989720800326298143504263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16659813866884198762336175 24989720800326298143504263)
      ·
        refine ⟨37484581200489447215256395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24989720800326298143504263 37484581200489447215256395)
        ·
          refine ⟨56226871800734170822884593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37484581200489447215256395 56226871800734170822884593)
          ·
            refine ⟨42170153850550628117163445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56226871800734170822884593 42170153850550628117163445)
            ·
              refine ⟨3953451923489121385984073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42170153850550628117163445 3953451923489121385984073)
              ·
                refine ⟨2965088942616841039488055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953451923489121385984073 2965088942616841039488055)
                ·
                  refine ⟨4447633413925261559232083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965088942616841039488055 4447633413925261559232083)
                  ·
                    refine ⟨6671450120887892338848125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447633413925261559232083 6671450120887892338848125)
                    ·
                      refine ⟨2501793795332959627068047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671450120887892338848125 2501793795332959627068047)
                      ·
                        rfl

theorem cell23_4872226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_4872226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872226 prefixEnd_4872226 := by exact prefixLift 4872226
  have htrace : WordTrace (prefixWord ++ tailWord_4872226) baseStart_4872226 baseEnd_4872226 := by
    simpa [prefixWord, tailWord_4872226, baseEnd_4872226] using wordTrace_append hprefix tailTrace_4872226
  have hstable : (prefixWord ++ tailWord_4872226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872226).length < 2 ^ (prefixWord ++ tailWord_4872226).sum := by decide
  have hdescent : baseEnd_4872226 < baseStart_4872226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872242 : List Nat := [3, 2, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_4872242 : Nat := 118140960795 + 4872242 * 2 ^ 59
def prefixEnd_4872242 : Nat := 4983230072969 + 3 ^ 40 * 4872242 * 2
def baseEnd_4872242 : Nat := 833934003674477188155991

theorem tailTrace_4872242 : CollatzResearch.WordTrace tailWord_4872242 prefixEnd_4872242 833934003674477188155991 := by
  unfold tailWord_4872242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44426316203676705382708745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118470176543137881020556653 44426316203676705382708745)
  ·
    refine ⟨33319737152757529037031559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44426316203676705382708745 33319737152757529037031559)
    ·
      refine ⟨49979605729136293555547339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33319737152757529037031559 49979605729136293555547339)
      ·
        refine ⟨74969408593704440333321009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49979605729136293555547339 74969408593704440333321009)
        ·
          refine ⟨56227056445278330249990757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74969408593704440333321009 56227056445278330249990757)
          ·
            refine ⟨10542573083489686921873267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56227056445278330249990757 10542573083489686921873267)
            ·
              refine ⟨15813859625234530382809901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542573083489686921873267 15813859625234530382809901)
              ·
                refine ⟨5930197359462948893553713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15813859625234530382809901 5930197359462948893553713)
                ·
                  refine ⟨4447648019597211670165285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5930197359462948893553713 4447648019597211670165285)
                  ·
                    refine ⟨833934003674477188155991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447648019597211670165285 833934003674477188155991)
                    ·
                      rfl

theorem cell23_4872242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_4872242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872242 prefixEnd_4872242 := by exact prefixLift 4872242
  have htrace : WordTrace (prefixWord ++ tailWord_4872242) baseStart_4872242 baseEnd_4872242 := by
    simpa [prefixWord, tailWord_4872242, baseEnd_4872242] using wordTrace_append hprefix tailTrace_4872242
  have hstable : (prefixWord ++ tailWord_4872242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872242).length < 2 ^ (prefixWord ++ tailWord_4872242).sum := by decide
  have hdescent : baseEnd_4872242 < baseStart_4872242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872249 : List Nat := [1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4872249 : Nat := 118140960795 + 4872249 * 2 ^ 59
def prefixEnd_4872249 : Nat := 4983230072969 + 3 ^ 40 * 4872249 * 2
def baseEnd_4872249 : Nat := 2501805605388013037080441

theorem tailTrace_4872249 : CollatzResearch.WordTrace tailWord_4872249 prefixEnd_4872249 2501805605388013037080441 := by
  unfold tailWord_4872249
  simp only [CollatzResearch.WordTrace]
  refine ⟨177705520125681461726339801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118470346750454307817559867 177705520125681461726339801)
  ·
    refine ⟨133279140094261096294754851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177705520125681461726339801 133279140094261096294754851)
    ·
      refine ⟨199918710141391644442132277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133279140094261096294754851 199918710141391644442132277)
      ·
        refine ⟨18742379075755466666449901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199918710141391644442132277 18742379075755466666449901)
        ·
          refine ⟨7028392153408299999918713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18742379075755466666449901 7028392153408299999918713)
          ·
            refine ⟨5271294115056224999939035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7028392153408299999918713 5271294115056224999939035)
            ·
              refine ⟨7906941172584337499908553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271294115056224999939035 7906941172584337499908553)
              ·
                refine ⟨5930205879438253124931415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7906941172584337499908553 5930205879438253124931415)
                ·
                  refine ⟨8895308819157379687397123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930205879438253124931415 8895308819157379687397123)
                  ·
                    refine ⟨13342963228736069531095685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8895308819157379687397123 13342963228736069531095685)
                    ·
                      refine ⟨2501805605388013037080441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13342963228736069531095685 2501805605388013037080441)
                      ·
                        rfl

theorem cell23_4872249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4872249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872249 prefixEnd_4872249 := by exact prefixLift 4872249
  have htrace : WordTrace (prefixWord ++ tailWord_4872249) baseStart_4872249 baseEnd_4872249 := by
    simpa [prefixWord, tailWord_4872249, baseEnd_4872249] using wordTrace_append hprefix tailTrace_4872249
  have hstable : (prefixWord ++ tailWord_4872249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872249).length < 2 ^ (prefixWord ++ tailWord_4872249).sum := by decide
  have hdescent : baseEnd_4872249 < baseStart_4872249 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872265 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 3]
def baseStart_4872265 : Nat := 118140960795 + 4872265 * 2 ^ 59
def prefixEnd_4872265 : Nat := 4983230072969 + 3 ^ 40 * 4872265 * 2
def baseEnd_4872265 : Nat := 2501813821078484974480367

theorem tailTrace_4872265 : CollatzResearch.WordTrace tailWord_4872265 prefixEnd_4872265 2501813821078484974480367 := by
  unfold tailWord_4872265
  simp only [CollatzResearch.WordTrace]
  refine ⟨177706103693623496458922249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118470735795748997639281499 177706103693623496458922249)
  ·
    refine ⟨133279577770217622344191687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177706103693623496458922249 133279577770217622344191687)
    ·
      refine ⟨199919366655326433516287531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133279577770217622344191687 199919366655326433516287531)
      ·
        refine ⟨299879049982989650274431297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199919366655326433516287531 299879049982989650274431297)
        ·
          refine ⟨224909287487242237705823473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299879049982989650274431297 224909287487242237705823473)
          ·
            refine ⟨168681965615431678279367605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224909287487242237705823473 168681965615431678279367605)
            ·
              refine ⟨15813934276446719838690713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168681965615431678279367605 15813934276446719838690713)
              ·
                refine ⟨11860450707335039879018035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15813934276446719838690713 11860450707335039879018035)
                ·
                  refine ⟨17790676061002559818527053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11860450707335039879018035 17790676061002559818527053)
                  ·
                    refine ⟨6671503522875959931947645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17790676061002559818527053 6671503522875959931947645)
                    ·
                      refine ⟨2501813821078484974480367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671503522875959931947645 2501813821078484974480367)
                      ·
                        rfl

theorem cell23_4872265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 3, 3].length) (baseStart_4872265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872265 prefixEnd_4872265 := by exact prefixLift 4872265
  have htrace : WordTrace (prefixWord ++ tailWord_4872265) baseStart_4872265 baseEnd_4872265 := by
    simpa [prefixWord, tailWord_4872265, baseEnd_4872265] using wordTrace_append hprefix tailTrace_4872265
  have hstable : (prefixWord ++ tailWord_4872265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872265).length < 2 ^ (prefixWord ++ tailWord_4872265).sum := by decide
  have hdescent : baseEnd_4872265 < baseStart_4872265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872292 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_4872292 : Nat := 118140960795 + 4872292 * 2 ^ 59
def prefixEnd_4872292 : Nat := 4983230072969 + 3 ^ 40 * 4872292 * 2
def baseEnd_4872292 : Nat := 2501827685056156368842743

theorem tailTrace_4872292 : CollatzResearch.WordTrace tailWord_4872292 prefixEnd_4872292 2501827685056156368842743 := by
  unfold tailWord_4872292
  simp only [CollatzResearch.WordTrace]
  refine ⟨88853544232262840035077565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118471392309683786713436753 88853544232262840035077565)
  ·
    refine ⟨33320079087098565013154087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88853544232262840035077565 33320079087098565013154087)
    ·
      refine ⟨49980118630647847519731131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33320079087098565013154087 49980118630647847519731131)
      ·
        refine ⟨74970177945971771279596697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49980118630647847519731131 74970177945971771279596697)
        ·
          refine ⟨56227633459478828459697523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74970177945971771279596697 56227633459478828459697523)
          ·
            refine ⟨84341450189218242689546285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56227633459478828459697523 84341450189218242689546285)
            ·
              refine ⟨31628043820956841008579857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84341450189218242689546285 31628043820956841008579857)
              ·
                refine ⟨23721032865717630756434893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31628043820956841008579857 23721032865717630756434893)
                ·
                  refine ⟨8895387324644111533663085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23721032865717630756434893 8895387324644111533663085)
                  ·
                    refine ⟨3335770246741541825123657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8895387324644111533663085 3335770246741541825123657)
                    ·
                      refine ⟨2501827685056156368842743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335770246741541825123657 2501827685056156368842743)
                      ·
                        rfl

theorem cell23_4872292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_4872292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872292 prefixEnd_4872292 := by exact prefixLift 4872292
  have htrace : WordTrace (prefixWord ++ tailWord_4872292) baseStart_4872292 baseEnd_4872292 := by
    simpa [prefixWord, tailWord_4872292, baseEnd_4872292] using wordTrace_append hprefix tailTrace_4872292
  have hstable : (prefixWord ++ tailWord_4872292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872292).length < 2 ^ (prefixWord ++ tailWord_4872292).sum := by decide
  have hdescent : baseEnd_4872292 < baseStart_4872292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872356 : List Nat := [2, 3, 1, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_4872356 : Nat := 118140960795 + 4872356 * 2 ^ 59
def prefixEnd_4872356 : Nat := 4983230072969 + 3 ^ 40 * 4872356 * 2
def baseEnd_4872356 : Nat := 2501860547818044118442449

theorem tailTrace_4872356 : CollatzResearch.WordTrace tailWord_4872356 prefixEnd_4872356 2501860547818044118442449 := by
  unfold tailWord_4872356
  simp only [CollatzResearch.WordTrace]
  refine ⟨88854711368146909500242461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118472948490862546000323281 88854711368146909500242461)
  ·
    refine ⟨33320516763055091062590923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88854711368146909500242461 33320516763055091062590923)
    ·
      refine ⟨49980775144582636593886385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33320516763055091062590923 49980775144582636593886385)
      ·
        refine ⟨37485581358436977445414789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49980775144582636593886385 37485581358436977445414789)
        ·
          refine ⟨7028546504706933271015273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37485581358436977445414789 7028546504706933271015273)
          ·
            refine ⟨5271409878530199953261455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7028546504706933271015273 5271409878530199953261455)
            ·
              refine ⟨7907114817795299929892183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271409878530199953261455 7907114817795299929892183)
              ·
                refine ⟨11860672226692949894838275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7907114817795299929892183 11860672226692949894838275)
                ·
                  refine ⟨17791008340039424842257413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11860672226692949894838275 17791008340039424842257413)
                  ·
                    refine ⟨3335814063757392157923265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17791008340039424842257413 3335814063757392157923265)
                    ·
                      refine ⟨2501860547818044118442449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335814063757392157923265 2501860547818044118442449)
                      ·
                        rfl

theorem cell23_4872356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_4872356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872356 prefixEnd_4872356 := by exact prefixLift 4872356
  have htrace : WordTrace (prefixWord ++ tailWord_4872356) baseStart_4872356 baseEnd_4872356 := by
    simpa [prefixWord, tailWord_4872356, baseEnd_4872356] using wordTrace_append hprefix tailTrace_4872356
  have hstable : (prefixWord ++ tailWord_4872356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872356).length < 2 ^ (prefixWord ++ tailWord_4872356).sum := by decide
  have hdescent : baseEnd_4872356 < baseStart_4872356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872375 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 1, 7]
def baseStart_4872375 : Nat := 118140960795 + 4872375 * 2 ^ 59
def prefixEnd_4872375 : Nat := 4983230072969 + 3 ^ 40 * 4872375 * 2
def baseEnd_4872375 : Nat := 833956767983493181368287

theorem tailTrace_4872375 : CollatzResearch.WordTrace tailWord_4872375 prefixEnd_4872375 833956767983493181368287 := by
  unfold tailWord_4872375
  simp only [CollatzResearch.WordTrace]
  refine ⟨177710115723224985245426579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118473410482149990163617719 177710115723224985245426579)
  ·
    refine ⟨266565173584837477868139869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177710115723224985245426579 266565173584837477868139869)
    ·
      refine ⟨99961940094314054200552451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266565173584837477868139869 99961940094314054200552451)
      ·
        refine ⟨149942910141471081300828677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99961940094314054200552451 149942910141471081300828677)
        ·
          refine ⟨28114295651525827743905377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149942910141471081300828677 28114295651525827743905377)
          ·
            refine ⟨21085721738644370807929033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28114295651525827743905377 21085721738644370807929033)
            ·
              refine ⟨15814291303983278105946775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21085721738644370807929033 15814291303983278105946775)
              ·
                refine ⟨23721436955974917158920163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15814291303983278105946775 23721436955974917158920163)
                ·
                  refine ⟨35582155433962375738380245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23721436955974917158920163 35582155433962375738380245)
                  ·
                    refine ⟨833956767983493181368287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35582155433962375738380245 833956767983493181368287)
                    ·
                      rfl

theorem cell23_4872375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_4872375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872375 prefixEnd_4872375 := by exact prefixLift 4872375
  have htrace : WordTrace (prefixWord ++ tailWord_4872375) baseStart_4872375 baseEnd_4872375 := by
    simpa [prefixWord, tailWord_4872375, baseEnd_4872375] using wordTrace_append hprefix tailTrace_4872375
  have hstable : (prefixWord ++ tailWord_4872375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872375).length < 2 ^ (prefixWord ++ tailWord_4872375).sum := by decide
  have hdescent : baseEnd_4872375 < baseStart_4872375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872396 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 7]
def baseStart_4872396 : Nat := 118140960795 + 4872396 * 2 ^ 59
def prefixEnd_4872396 : Nat := 4983230072969 + 3 ^ 40 * 4872396 * 2
def baseEnd_4872396 : Nat := 277986787449358217993585

theorem tailTrace_4872396 : CollatzResearch.WordTrace tailWord_4872396 prefixEnd_4872396 277986787449358217993585 := by
  unfold tailWord_4872396
  simp only [CollatzResearch.WordTrace]
  refine ⟨88855440828074452915970521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118473921104099270554627361 88855440828074452915970521)
  ·
    refine ⟨66641580621055839686977891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88855440828074452915970521 66641580621055839686977891)
    ·
      refine ⟨99962370931583759530466837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66641580621055839686977891 99962370931583759530466837)
      ·
        refine ⟨4685736137417988727990633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99962370931583759530466837 4685736137417988727990633)
        ·
          refine ⟨3514302103063491545992975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685736137417988727990633 3514302103063491545992975)
          ·
            refine ⟨5271453154595237318989463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514302103063491545992975 5271453154595237318989463)
            ·
              refine ⟨7907179731892855978484195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271453154595237318989463 7907179731892855978484195)
              ·
                refine ⟨11860769597839283967726293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7907179731892855978484195 11860769597839283967726293)
                ·
                  refine ⟨277986787449358217993585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11860769597839283967726293 277986787449358217993585)
                  ·
                    rfl

theorem cell23_4872396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_4872396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872396 prefixEnd_4872396 := by exact prefixLift 4872396
  have htrace : WordTrace (prefixWord ++ tailWord_4872396) baseStart_4872396 baseEnd_4872396 := by
    simpa [prefixWord, tailWord_4872396, baseEnd_4872396] using wordTrace_append hprefix tailTrace_4872396
  have hstable : (prefixWord ++ tailWord_4872396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872396).length < 2 ^ (prefixWord ++ tailWord_4872396).sum := by decide
  have hdescent : baseEnd_4872396 < baseStart_4872396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872402 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_4872402 : Nat := 118140960795 + 4872402 * 2 ^ 59
def prefixEnd_4872402 : Nat := 4983230072969 + 3 ^ 40 * 4872402 * 2
def baseEnd_4872402 : Nat := 2501884167928150938467237

theorem tailTrace_4872402 : CollatzResearch.WordTrace tailWord_4872402 prefixEnd_4872402 2501884167928150938467237 := by
  unfold tailWord_4872402
  simp only [CollatzResearch.WordTrace]
  refine ⟨44427775123531792214164865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118474066996084779237772973 44427775123531792214164865)
  ·
    refine ⟨33320831342648844160623649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44427775123531792214164865 33320831342648844160623649)
    ·
      refine ⟨24990623506986633120467737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33320831342648844160623649 24990623506986633120467737)
      ·
        refine ⟨18742967630239974840350803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24990623506986633120467737 18742967630239974840350803)
        ·
          refine ⟨28114451445359962260526205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18742967630239974840350803 28114451445359962260526205)
          ·
            refine ⟨10542919292009985847697327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28114451445359962260526205 10542919292009985847697327)
            ·
              refine ⟨15814378938014978771545991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10542919292009985847697327 15814378938014978771545991)
              ·
                refine ⟨23721568407022468157318987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15814378938014978771545991 23721568407022468157318987)
                ·
                  refine ⟨35582352610533702235978481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23721568407022468157318987 35582352610533702235978481)
                  ·
                    refine ⟨26686764457900276676983861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35582352610533702235978481 26686764457900276676983861)
                    ·
                      refine ⟨2501884167928150938467237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26686764457900276676983861 2501884167928150938467237)
                      ·
                        rfl

theorem cell23_4872402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_4872402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872402 prefixEnd_4872402 := by exact prefixLift 4872402
  have htrace : WordTrace (prefixWord ++ tailWord_4872402) baseStart_4872402 baseEnd_4872402 := by
    simpa [prefixWord, tailWord_4872402, baseEnd_4872402] using wordTrace_append hprefix tailTrace_4872402
  have hstable : (prefixWord ++ tailWord_4872402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872402).length < 2 ^ (prefixWord ++ tailWord_4872402).sum := by decide
  have hdescent : baseEnd_4872402 < baseStart_4872402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872456 : List Nat := [2, 1, 3, 2, 3, 2, 1, 4, 1, 4]
def baseStart_4872456 : Nat := 118140960795 + 4872456 * 2 ^ 59
def prefixEnd_4872456 : Nat := 4983230072969 + 3 ^ 40 * 4872456 * 2
def baseEnd_4872456 : Nat := 833970631961164575730663

theorem tailTrace_4872456 : CollatzResearch.WordTrace tailWord_4872456 prefixEnd_4872456 833970631961164575730663 := by
  unfold tailWord_4872456
  simp only [CollatzResearch.WordTrace]
  refine ⟨88856535017965768039562611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118475380023954357386083481 88856535017965768039562611)
  ·
    refine ⟨133284802526948652059343917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88856535017965768039562611 133284802526948652059343917)
    ·
      refine ⟨49981800947605744522253969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133284802526948652059343917 49981800947605744522253969)
      ·
        refine ⟨37486350710704308391690477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49981800947605744522253969 37486350710704308391690477)
        ·
          refine ⟨14057381516514115646883929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37486350710704308391690477 14057381516514115646883929)
          ·
            refine ⟨10543036137385586735162947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14057381516514115646883929 10543036137385586735162947)
            ·
              refine ⟨15814554206078380102744421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10543036137385586735162947 15814554206078380102744421)
              ·
                refine ⟨2965228913639696269264579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15814554206078380102744421 2965228913639696269264579)
                ·
                  refine ⟨4447843370459544403896869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965228913639696269264579 4447843370459544403896869)
                  ·
                    refine ⟨833970631961164575730663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4447843370459544403896869 833970631961164575730663)
                    ·
                      rfl

theorem cell23_4872456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 4, 1, 4].length) (baseStart_4872456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872456 prefixEnd_4872456 := by exact prefixLift 4872456
  have htrace : WordTrace (prefixWord ++ tailWord_4872456) baseStart_4872456 baseEnd_4872456 := by
    simpa [prefixWord, tailWord_4872456, baseEnd_4872456] using wordTrace_append hprefix tailTrace_4872456
  have hstable : (prefixWord ++ tailWord_4872456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872456).length < 2 ^ (prefixWord ++ tailWord_4872456).sum := by decide
  have hdescent : baseEnd_4872456 < baseStart_4872456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872479 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 3]
def baseStart_4872479 : Nat := 118140960795 + 4872479 * 2 ^ 59
def prefixEnd_4872479 : Nat := 4983230072969 + 3 ^ 40 * 4872479 * 2
def baseEnd_4872479 : Nat := 2501923705938547137204383

theorem tailTrace_4872479 : CollatzResearch.WordTrace tailWord_4872479 prefixEnd_4872479 2501923705938547137204383 := by
  unfold tailWord_4872479
  simp only [CollatzResearch.WordTrace]
  refine ⟨177713908914848211007212491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118475939276565474004808327 177713908914848211007212491)
  ·
    refine ⟨266570863372272316510818737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177713908914848211007212491 266570863372272316510818737)
    ·
      refine ⟨199928147529204237383114053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266570863372272316510818737 199928147529204237383114053)
      ·
        refine ⟨37486527661725794509333885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199928147529204237383114053 37486527661725794509333885)
        ·
          refine ⟨14057447873147172941000207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37486527661725794509333885 14057447873147172941000207)
          ·
            refine ⟨21086171809720759411500311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14057447873147172941000207 21086171809720759411500311)
            ·
              refine ⟨31629257714581139117250467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21086171809720759411500311 31629257714581139117250467)
              ·
                refine ⟨47443886571871708675875701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31629257714581139117250467 47443886571871708675875701)
                ·
                  refine ⟨4447864366112972688363347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47443886571871708675875701 4447864366112972688363347)
                  ·
                    refine ⟨6671796549169459032545021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447864366112972688363347 6671796549169459032545021)
                    ·
                      refine ⟨2501923705938547137204383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671796549169459032545021 2501923705938547137204383)
                      ·
                        rfl

theorem cell23_4872479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_4872479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872479 prefixEnd_4872479 := by exact prefixLift 4872479
  have htrace : WordTrace (prefixWord ++ tailWord_4872479) baseStart_4872479 baseEnd_4872479 := by
    simpa [prefixWord, tailWord_4872479, baseEnd_4872479] using wordTrace_append hprefix tailTrace_4872479
  have hstable : (prefixWord ++ tailWord_4872479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872479).length < 2 ^ (prefixWord ++ tailWord_4872479).sum := by decide
  have hdescent : baseEnd_4872479 < baseStart_4872479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872513 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 3]
def baseStart_4872513 : Nat := 118140960795 + 4872513 * 2 ^ 59
def prefixEnd_4872513 : Nat := 4983230072969 + 3 ^ 40 * 4872513 * 2
def baseEnd_4872513 : Nat := 2501941164280800004179227

theorem tailTrace_4872513 : CollatzResearch.WordTrace tailWord_4872513 prefixEnd_4872513 2501941164280800004179227 := by
  unfold tailWord_4872513
  simp only [CollatzResearch.WordTrace]
  refine ⟨177715148996725034813950193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118476765997816689875966795 177715148996725034813950193)
  ·
    refine ⟨133286361747543776110462645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177715148996725034813950193 133286361747543776110462645)
    ·
      refine ⟨12495596413832229010355873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133286361747543776110462645 12495596413832229010355873)
      ·
        refine ⟨9371697310374171757766905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12495596413832229010355873 9371697310374171757766905)
        ·
          refine ⟨7028772982780628818325179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9371697310374171757766905 7028772982780628818325179)
          ·
            refine ⟨10543159474170943227487769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028772982780628818325179 10543159474170943227487769)
            ·
              refine ⟨7907369605628207420615827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10543159474170943227487769 7907369605628207420615827)
              ·
                refine ⟨11861054408442311130923741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7907369605628207420615827 11861054408442311130923741)
                ·
                  refine ⟨4447895403165866674096403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11861054408442311130923741 4447895403165866674096403)
                  ·
                    refine ⟨6671843104748800011144605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4447895403165866674096403 6671843104748800011144605)
                    ·
                      refine ⟨2501941164280800004179227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6671843104748800011144605 2501941164280800004179227)
                      ·
                        rfl

theorem cell23_4872513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_4872513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872513 prefixEnd_4872513 := by exact prefixLift 4872513
  have htrace : WordTrace (prefixWord ++ tailWord_4872513) baseStart_4872513 baseEnd_4872513 := by
    simpa [prefixWord, tailWord_4872513, baseEnd_4872513] using wordTrace_append hprefix tailTrace_4872513
  have hstable : (prefixWord ++ tailWord_4872513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872513).length < 2 ^ (prefixWord ++ tailWord_4872513).sum := by decide
  have hdescent : baseEnd_4872513 < baseStart_4872513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872529 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 1, 6]
def baseStart_4872529 : Nat := 118140960795 + 4872529 * 2 ^ 59
def prefixEnd_4872529 : Nat := 4983230072969 + 3 ^ 40 * 4872529 * 2
def baseEnd_4872529 : Nat := 833983126657090647193051

theorem tailTrace_4872529 : CollatzResearch.WordTrace tailWord_4872529 prefixEnd_4872529 833983126657090647193051 := by
  unfold tailWord_4872529
  simp only [CollatzResearch.WordTrace]
  refine ⟨177715732564667069546532641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118477155043111379697688427 177715732564667069546532641)
  ·
    refine ⟨133286799423500302159899481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177715732564667069546532641 133286799423500302159899481)
    ·
      refine ⟨99965099567625226619924611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133286799423500302159899481 99965099567625226619924611)
      ·
        refine ⟨149947649351437839929886917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99965099567625226619924611 149947649351437839929886917)
        ·
          refine ⟨28115184253394594986853797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149947649351437839929886917 28115184253394594986853797)
          ·
            refine ⟨5271597047511486560035087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28115184253394594986853797 5271597047511486560035087)
            ·
              refine ⟨7907395571267229840052631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271597047511486560035087 7907395571267229840052631)
              ·
                refine ⟨11861093356900844760078947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7907395571267229840052631 11861093356900844760078947)
                ·
                  refine ⟨17791640035351267140118421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11861093356900844760078947 17791640035351267140118421)
                  ·
                    refine ⟨833983126657090647193051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17791640035351267140118421 833983126657090647193051)
                    ·
                      rfl

theorem cell23_4872529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 1, 6].length) (baseStart_4872529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872529 prefixEnd_4872529 := by exact prefixLift 4872529
  have htrace : WordTrace (prefixWord ++ tailWord_4872529) baseStart_4872529 baseEnd_4872529 := by
    simpa [prefixWord, tailWord_4872529, baseEnd_4872529] using wordTrace_append hprefix tailTrace_4872529
  have hstable : (prefixWord ++ tailWord_4872529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872529).length < 2 ^ (prefixWord ++ tailWord_4872529).sum := by decide
  have hdescent : baseEnd_4872529 < baseStart_4872529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872613 : List Nat := [1, 3, 1, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_4872613 : Nat := 118140960795 + 4872613 * 2 ^ 59
def prefixEnd_4872613 : Nat := 4983230072969 + 3 ^ 40 * 4872613 * 2
def baseEnd_4872613 : Nat := 2501992512346249612928767

theorem tailTrace_4872613 : CollatzResearch.WordTrace tailWord_4872613 prefixEnd_4872613 2501992512346249612928767 := by
  unfold tailWord_4872613
  simp only [CollatzResearch.WordTrace]
  refine ⟨177718796296362751892590493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118479197530908501261726995 177718796296362751892590493)
  ·
    refine ⟨66644548611136031959721435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177718796296362751892590493 66644548611136031959721435)
    ·
      refine ⟨99966822916704047939582153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66644548611136031959721435 99966822916704047939582153)
      ·
        refine ⟨74975117187528035954686615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99966822916704047939582153 74975117187528035954686615)
        ·
          refine ⟨112462675781292053932029923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74975117187528035954686615 112462675781292053932029923)
          ·
            refine ⟨168694013671938080898044885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112462675781292053932029923 168694013671938080898044885)
            ·
              refine ⟨3953765945436048771047927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 168694013671938080898044885 3953765945436048771047927)
              ·
                refine ⟨5930648918154073156571891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3953765945436048771047927 5930648918154073156571891)
                ·
                  refine ⟨8895973377231109734857837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5930648918154073156571891 8895973377231109734857837)
                  ·
                    refine ⟨3335990016461666150571689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8895973377231109734857837 3335990016461666150571689)
                    ·
                      refine ⟨2501992512346249612928767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335990016461666150571689 2501992512346249612928767)
                      ·
                        rfl

theorem cell23_4872613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_4872613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872613 prefixEnd_4872613 := by exact prefixLift 4872613
  have htrace : WordTrace (prefixWord ++ tailWord_4872613) baseStart_4872613 baseEnd_4872613 := by
    simpa [prefixWord, tailWord_4872613, baseEnd_4872613] using wordTrace_append hprefix tailTrace_4872613
  have hstable : (prefixWord ++ tailWord_4872613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872613).length < 2 ^ (prefixWord ++ tailWord_4872613).sum := by decide
  have hdescent : baseEnd_4872613 < baseStart_4872613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872621 : List Nat := [1, 5, 2, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_4872621 : Nat := 118140960795 + 4872621 * 2 ^ 59
def prefixEnd_4872621 : Nat := 4983230072969 + 3 ^ 40 * 4872621 * 2
def baseEnd_4872621 : Nat := 2501996620191485581628731

theorem tailTrace_4872621 : CollatzResearch.WordTrace tailWord_4872621 prefixEnd_4872621 2501996620191485581628731 := by
  unfold tailWord_4872621
  simp only [CollatzResearch.WordTrace]
  refine ⟨177719088080333769258881717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118479392053555846172587811 177719088080333769258881717)
  ·
    refine ⟨16661164507531290868020161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177719088080333769258881717 16661164507531290868020161)
    ·
      refine ⟨12495873380648468151015121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16661164507531290868020161 12495873380648468151015121)
      ·
        refine ⟨9371905035486351113261341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12495873380648468151015121 9371905035486351113261341)
        ·
          refine ⟨3514464388307381667473003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9371905035486351113261341 3514464388307381667473003)
          ·
            refine ⟨5271696582461072501209505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3514464388307381667473003 5271696582461072501209505)
            ·
              refine ⟨3953772436845804375907129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5271696582461072501209505 3953772436845804375907129)
              ·
                refine ⟨2965329327634353281930347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3953772436845804375907129 2965329327634353281930347)
                ·
                  refine ⟨4447993991451529922895521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965329327634353281930347 4447993991451529922895521)
                  ·
                    refine ⟨3335995493588647442171641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4447993991451529922895521 3335995493588647442171641)
                    ·
                      refine ⟨2501996620191485581628731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3335995493588647442171641 2501996620191485581628731)
                      ·
                        rfl

theorem cell23_4872621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_4872621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872621 prefixEnd_4872621 := by exact prefixLift 4872621
  have htrace : WordTrace (prefixWord ++ tailWord_4872621) baseStart_4872621 baseEnd_4872621 := by
    simpa [prefixWord, tailWord_4872621, baseEnd_4872621] using wordTrace_append hprefix tailTrace_4872621
  have hstable : (prefixWord ++ tailWord_4872621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872621).length < 2 ^ (prefixWord ++ tailWord_4872621).sum := by decide
  have hdescent : baseEnd_4872621 < baseStart_4872621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872632 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 7]
def baseStart_4872632 : Nat := 118140960795 + 4872632 * 2 ^ 59
def prefixEnd_4872632 : Nat := 4983230072969 + 3 ^ 40 * 4872632 * 2
def baseEnd_4872632 : Nat := 278000252053187226510131

theorem tailTrace_4872632 : CollatzResearch.WordTrace tailWord_4872632 prefixEnd_4872632 278000252053187226510131 := by
  unfold tailWord_4872632
  simp only [CollatzResearch.WordTrace]
  refine ⟨88859744641646959068766075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118479659522195945425021433 88859744641646959068766075)
  ·
    refine ⟨133289616962470438603149113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88859744641646959068766075 133289616962470438603149113)
    ·
      refine ⟨99967212721852828952361835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133289616962470438603149113 99967212721852828952361835)
      ·
        refine ⟨149950819082779243428542753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99967212721852828952361835 149950819082779243428542753)
        ·
          refine ⟨112463114312084432571407065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149950819082779243428542753 112463114312084432571407065)
          ·
            refine ⟨84347335734063324428555299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112463114312084432571407065 84347335734063324428555299)
            ·
              refine ⟨126521003601094986642832949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84347335734063324428555299 126521003601094986642832949)
              ·
                refine ⟨11861344087602654997765589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126521003601094986642832949 11861344087602654997765589)
                ·
                  refine ⟨278000252053187226510131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11861344087602654997765589 278000252053187226510131)
                  ·
                    rfl

theorem cell23_4872632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 7].length) (baseStart_4872632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872632 prefixEnd_4872632 := by exact prefixLift 4872632
  have htrace : WordTrace (prefixWord ++ tailWord_4872632) baseStart_4872632 baseEnd_4872632 := by
    simpa [prefixWord, tailWord_4872632, baseEnd_4872632] using wordTrace_append hprefix tailTrace_4872632
  have hstable : (prefixWord ++ tailWord_4872632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872632).length < 2 ^ (prefixWord ++ tailWord_4872632).sum := by decide
  have hdescent : baseEnd_4872632 < baseStart_4872632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872666 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 5]
def baseStart_4872666 : Nat := 118140960795 + 4872666 * 2 ^ 59
def prefixEnd_4872666 : Nat := 4983230072969 + 3 ^ 40 * 4872666 * 2
def baseEnd_4872666 : Nat := 278002191868993100618447

theorem tailTrace_4872666 : CollatzResearch.WordTrace tailWord_4872666 prefixEnd_4872666 278002191868993100618447 := by
  unfold tailWord_4872666
  simp only [CollatzResearch.WordTrace]
  refine ⟨44430182341292685486067463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118480486243447161296179901 44430182341292685486067463)
  ·
    refine ⟨66645273511939028229101195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44430182341292685486067463 66645273511939028229101195)
    ·
      refine ⟨99967910267908542343651793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66645273511939028229101195 99967910267908542343651793)
      ·
        refine ⟨74975932700931406757738845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99967910267908542343651793 74975932700931406757738845)
        ·
          refine ⟨28115974762849277534152067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74975932700931406757738845 28115974762849277534152067)
          ·
            refine ⟨42173962144273916301228101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28115974762849277534152067 42173962144273916301228101)
            ·
              refine ⟨7907617902051359306480269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42173962144273916301228101 7907617902051359306480269)
              ·
                refine ⟨2965356713269259739930101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7907617902051359306480269 2965356713269259739930101)
                ·
                  refine ⟨278002191868993100618447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2965356713269259739930101 278002191868993100618447)
                  ·
                    rfl

theorem cell23_4872666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_4872666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872666 prefixEnd_4872666 := by exact prefixLift 4872666
  have htrace : WordTrace (prefixWord ++ tailWord_4872666) baseStart_4872666 baseEnd_4872666 := by
    simpa [prefixWord, tailWord_4872666, baseEnd_4872666] using wordTrace_append hprefix tailTrace_4872666
  have hstable : (prefixWord ++ tailWord_4872666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872666).length < 2 ^ (prefixWord ++ tailWord_4872666).sum := by decide
  have hdescent : baseEnd_4872666 < baseStart_4872666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872677 : List Nat := [1, 3, 1, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4872677 : Nat := 118140960795 + 4872677 * 2 ^ 59
def prefixEnd_4872677 : Nat := 4983230072969 + 3 ^ 40 * 4872677 * 2
def baseEnd_4872677 : Nat := 2502025375108137362528473

theorem tailTrace_4872677 : CollatzResearch.WordTrace tailWord_4872677 prefixEnd_4872677 2502025375108137362528473 := by
  unfold tailWord_4872677
  simp only [CollatzResearch.WordTrace]
  refine ⟨177721130568130890822920285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118480753712087260548613523 177721130568130890822920285)
  ·
    refine ⟨66645423963049084058595107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177721130568130890822920285 66645423963049084058595107)
    ·
      refine ⟨99968135944573626087892661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66645423963049084058595107 99968135944573626087892661)
      ·
        refine ⟨9372012744803777445739937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99968135944573626087892661 9372012744803777445739937)
        ·
          refine ⟨7029009558602833084304953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9372012744803777445739937 7029009558602833084304953)
          ·
            refine ⟨5271757168952124813228715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7029009558602833084304953 5271757168952124813228715)
            ·
              refine ⟨7907635753428187219843073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271757168952124813228715 7907635753428187219843073)
              ·
                refine ⟨5930726815071140414882305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7907635753428187219843073 5930726815071140414882305)
                ·
                  refine ⟨4448045111303355311161729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5930726815071140414882305 4448045111303355311161729)
                  ·
                    refine ⟨3336033833477516483371297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4448045111303355311161729 3336033833477516483371297)
                    ·
                      refine ⟨2502025375108137362528473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336033833477516483371297 2502025375108137362528473)
                      ·
                        rfl

theorem cell23_4872677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4872677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872677 prefixEnd_4872677 := by exact prefixLift 4872677
  have htrace : WordTrace (prefixWord ++ tailWord_4872677) baseStart_4872677 baseEnd_4872677 := by
    simpa [prefixWord, tailWord_4872677, baseEnd_4872677] using wordTrace_append hprefix tailTrace_4872677
  have hstable : (prefixWord ++ tailWord_4872677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872677).length < 2 ^ (prefixWord ++ tailWord_4872677).sum := by decide
  have hdescent : baseEnd_4872677 < baseStart_4872677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872679 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 4, 5]
def baseStart_4872679 : Nat := 118140960795 + 4872679 * 2 ^ 59
def prefixEnd_4872679 : Nat := 4983230072969 + 3 ^ 40 * 4872679 * 2
def baseEnd_4872679 : Nat := 834008800689815451567821

theorem tailTrace_4872679 : CollatzResearch.WordTrace tailWord_4872679 prefixEnd_4872679 834008800689815451567821 := by
  unfold tailWord_4872679
  simp only [CollatzResearch.WordTrace]
  refine ⟨177721203514123645164493091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118480802342749096776328727 177721203514123645164493091)
  ·
    refine ⟨266581805271185467746739637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177721203514123645164493091 266581805271185467746739637)
    ·
      refine ⟨24992044244173637601256841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266581805271185467746739637 24992044244173637601256841)
      ·
        refine ⟨18744033183130228200942631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24992044244173637601256841 18744033183130228200942631)
        ·
          refine ⟨28116049774695342301413947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18744033183130228200942631 28116049774695342301413947)
          ·
            refine ⟨42174074662043013452120921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28116049774695342301413947 42174074662043013452120921)
            ·
              refine ⟨31630555996532260089090691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42174074662043013452120921 31630555996532260089090691)
              ·
                refine ⟨47445833994798390133636037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31630555996532260089090691 47445833994798390133636037)
                ·
                  refine ⟨8896093874024698150056757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47445833994798390133636037 8896093874024698150056757)
                  ·
                    refine ⟨834008800689815451567821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8896093874024698150056757 834008800689815451567821)
                    ·
                      rfl

theorem cell23_4872679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_4872679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872679 prefixEnd_4872679 := by exact prefixLift 4872679
  have htrace : WordTrace (prefixWord ++ tailWord_4872679) baseStart_4872679 baseEnd_4872679 := by
    simpa [prefixWord, tailWord_4872679, baseEnd_4872679] using wordTrace_append hprefix tailTrace_4872679
  have hstable : (prefixWord ++ tailWord_4872679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872679).length < 2 ^ (prefixWord ++ tailWord_4872679).sum := by decide
  have hdescent : baseEnd_4872679 < baseStart_4872679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872717 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 5]
def baseStart_4872717 : Nat := 118140960795 + 4872717 * 2 ^ 59
def prefixEnd_4872717 : Nat := 4983230072969 + 3 ^ 40 * 4872717 * 2
def baseEnd_4872717 : Nat := 278005101592701911780921

theorem tailTrace_4872717 : CollatzResearch.WordTrace tailWord_4872717 prefixEnd_4872717 278005101592701911780921 := by
  unfold tailWord_4872717
  simp only [CollatzResearch.WordTrace]
  refine ⟨177722589487985977654376405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118481726325323985102917603 177722589487985977654376405)
  ·
    refine ⟨4165373191124671351274447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 177722589487985977654376405 4165373191124671351274447)
    ·
      refine ⟨6248059786687007026911671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4165373191124671351274447 6248059786687007026911671)
      ·
        refine ⟨9372089680030510540367507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248059786687007026911671 9372089680030510540367507)
        ·
          refine ⟨14058134520045765810551261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372089680030510540367507 14058134520045765810551261)
          ·
            refine ⟨5271800445017162178956723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14058134520045765810551261 5271800445017162178956723)
            ·
              refine ⟨7907700667525743268435085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5271800445017162178956723 7907700667525743268435085)
              ·
                refine ⟨2965387750322153725663157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7907700667525743268435085 2965387750322153725663157)
                ·
                  refine ⟨278005101592701911780921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2965387750322153725663157 278005101592701911780921)
                  ·
                    rfl

theorem cell23_4872717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_4872717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872717 prefixEnd_4872717 := by exact prefixLift 4872717
  have htrace : WordTrace (prefixWord ++ tailWord_4872717) baseStart_4872717 baseEnd_4872717 := by
    simpa [prefixWord, tailWord_4872717, baseEnd_4872717] using wordTrace_append hprefix tailTrace_4872717
  have hstable : (prefixWord ++ tailWord_4872717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872717).length < 2 ^ (prefixWord ++ tailWord_4872717).sum := by decide
  have hdescent : baseEnd_4872717 < baseStart_4872717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872739 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 8]
def baseStart_4872739 : Nat := 118140960795 + 4872739 * 2 ^ 59
def prefixEnd_4872739 : Nat := 4983230072969 + 3 ^ 40 * 4872739 * 2
def baseEnd_4872739 : Nat := 278006356767635124439243

theorem tailTrace_4872739 : CollatzResearch.WordTrace tailWord_4872739 prefixEnd_4872739 278006356767635124439243 := by
  unfold tailWord_4872739
  simp only [CollatzResearch.WordTrace]
  refine ⟨177723391893906275411677271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118482261262604183607784847 177723391893906275411677271)
  ·
    refine ⟨266585087840859413117515907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177723391893906275411677271 266585087840859413117515907)
    ·
      refine ⟨399877631761289119676273861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266585087840859413117515907 399877631761289119676273861)
      ·
        refine ⟨74977055955241709939301349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399877631761289119676273861 74977055955241709939301349)
        ·
          refine ⟨14058197991607820613619003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74977055955241709939301349 14058197991607820613619003)
          ·
            refine ⟨21087296987411730920428505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14058197991607820613619003 21087296987411730920428505)
            ·
              refine ⟨15815472740558798190321379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21087296987411730920428505 15815472740558798190321379)
              ·
                refine ⟨23723209110838197285482069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15815472740558798190321379 23723209110838197285482069)
                ·
                  refine ⟨278006356767635124439243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23723209110838197285482069 278006356767635124439243)
                  ·
                    rfl

theorem cell23_4872739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 8].length) (baseStart_4872739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872739 prefixEnd_4872739 := by exact prefixLift 4872739
  have htrace : WordTrace (prefixWord ++ tailWord_4872739) baseStart_4872739 baseEnd_4872739 := by
    simpa [prefixWord, tailWord_4872739, baseEnd_4872739] using wordTrace_append hprefix tailTrace_4872739
  have hstable : (prefixWord ++ tailWord_4872739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872739).length < 2 ^ (prefixWord ++ tailWord_4872739).sum := by decide
  have hdescent : baseEnd_4872739 < baseStart_4872739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872776 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2]
def baseStart_4872776 : Nat := 118140960795 + 4872776 * 2 ^ 59
def prefixEnd_4872776 : Nat := 4983230072969 + 3 ^ 40 * 4872776 * 2
def baseEnd_4872776 : Nat := 2502076209692932475190517

theorem tailTrace_4872776 : CollatzResearch.WordTrace tailWord_4872776 prefixEnd_4872776 2502076209692932475190517 := by
  unfold tailWord_4872776
  simp only [CollatzResearch.WordTrace]
  refine ⟨88862370697386115365387091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118483160929848153820516121 88862370697386115365387091)
  ·
    refine ⟨133293556046079173048080637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88862370697386115365387091 133293556046079173048080637)
    ·
      refine ⟨49985083517279689893030239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133293556046079173048080637 49985083517279689893030239)
      ·
        refine ⟨74977625275919534839545359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49985083517279689893030239 74977625275919534839545359)
        ·
          refine ⟨112466437913879302259318039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74977625275919534839545359 112466437913879302259318039)
          ·
            refine ⟨168699656870818953388977059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112466437913879302259318039 168699656870818953388977059)
            ·
              refine ⟨253049485306228430083465589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168699656870818953388977059 253049485306228430083465589)
              ·
                refine ⟨23723389247458915320324899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 253049485306228430083465589 23723389247458915320324899)
                ·
                  refine ⟨35585083871188372980487349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23723389247458915320324899 35585083871188372980487349)
                  ·
                    refine ⟨3336101612923909966920689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35585083871188372980487349 3336101612923909966920689)
                    ·
                      refine ⟨2502076209692932475190517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336101612923909966920689 2502076209692932475190517)
                      ·
                        rfl

theorem cell23_4872776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 1, 5, 2].length) (baseStart_4872776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872776 prefixEnd_4872776 := by exact prefixLift 4872776
  have htrace : WordTrace (prefixWord ++ tailWord_4872776) baseStart_4872776 baseEnd_4872776 := by
    simpa [prefixWord, tailWord_4872776, baseEnd_4872776] using wordTrace_append hprefix tailTrace_4872776
  have hstable : (prefixWord ++ tailWord_4872776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872776).length < 2 ^ (prefixWord ++ tailWord_4872776).sum := by decide
  have hdescent : baseEnd_4872776 < baseStart_4872776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872809 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 5]
def baseStart_4872809 : Nat := 118140960795 + 4872809 * 2 ^ 59
def prefixEnd_4872809 : Nat := 4983230072969 + 3 ^ 40 * 4872809 * 2
def baseEnd_4872809 : Nat := 2502093154554530846077865

theorem tailTrace_4872809 : CollatzResearch.WordTrace tailWord_4872809 prefixEnd_4872809 2502093154554530846077865 := by
  unfold tailWord_4872809
  simp only [CollatzResearch.WordTrace]
  refine ⟨177725945003652677366725481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118483963335768451577816987 177725945003652677366725481)
  ·
    refine ⟨133294458752739508025044111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177725945003652677366725481 133294458752739508025044111)
    ·
      refine ⟨199941688129109262037566167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133294458752739508025044111 199941688129109262037566167)
      ·
        refine ⟨299912532193663893056349251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199941688129109262037566167 299912532193663893056349251)
        ·
          refine ⟨449868798290495839584523877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299912532193663893056349251 449868798290495839584523877)
          ·
            refine ⟨84350399679467969922098227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 449868798290495839584523877 84350399679467969922098227)
            ·
              refine ⟨126525599519201954883147341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84350399679467969922098227 126525599519201954883147341)
              ·
                refine ⟨47447099819700733081180253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126525599519201954883147341 47447099819700733081180253)
                ·
                  refine ⟨17792662432387774905442595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47447099819700733081180253 17792662432387774905442595)
                  ·
                    refine ⟨26688993648581662358163893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17792662432387774905442595 26688993648581662358163893)
                    ·
                      refine ⟨2502093154554530846077865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26688993648581662358163893 2502093154554530846077865)
                      ·
                        rfl

theorem cell23_4872809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 1, 5].length) (baseStart_4872809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872809 prefixEnd_4872809 := by exact prefixLift 4872809
  have htrace : WordTrace (prefixWord ++ tailWord_4872809) baseStart_4872809 baseEnd_4872809 := by
    simpa [prefixWord, tailWord_4872809, baseEnd_4872809] using wordTrace_append hprefix tailTrace_4872809
  have hstable : (prefixWord ++ tailWord_4872809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872809).length < 2 ^ (prefixWord ++ tailWord_4872809).sum := by decide
  have hdescent : baseEnd_4872809 < baseStart_4872809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872823 : List Nat := [1, 1, 3, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_4872823 : Nat := 118140960795 + 4872823 * 2 ^ 59
def prefixEnd_4872823 : Nat := 4983230072969 + 3 ^ 40 * 4872823 * 2
def baseEnd_4872823 : Nat := 2502100343283693791302801

theorem tailTrace_4872823 : CollatzResearch.WordTrace tailWord_4872823 prefixEnd_4872823 2502100343283693791302801 := by
  unfold tailWord_4872823
  simp only [CollatzResearch.WordTrace]
  refine ⟨177726455625601957757735123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118484303750401305171823415 177726455625601957757735123)
  ·
    refine ⟨266589683438402936636602685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177726455625601957757735123 266589683438402936636602685)
    ·
      refine ⟨99971131289401101238726007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266589683438402936636602685 99971131289401101238726007)
      ·
        refine ⟨149956696934101651858089011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99971131289401101238726007 149956696934101651858089011)
        ·
          refine ⟨224935045401152477787133517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149956696934101651858089011 224935045401152477787133517)
          ·
            refine ⟨84350642025432179170175069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 224935045401152477787133517 84350642025432179170175069)
            ·
              refine ⟨31631490759537067188815651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84350642025432179170175069 31631490759537067188815651)
              ·
                refine ⟨47447236139305600783223477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31631490759537067188815651 47447236139305600783223477)
                ·
                  refine ⟨4448178388059900073427201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47447236139305600783223477 4448178388059900073427201)
                  ·
                    refine ⟨3336133791044925055070401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4448178388059900073427201 3336133791044925055070401)
                    ·
                      refine ⟨2502100343283693791302801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336133791044925055070401 2502100343283693791302801)
                      ·
                        rfl

theorem cell23_4872823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_4872823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872823 prefixEnd_4872823 := by exact prefixLift 4872823
  have htrace : WordTrace (prefixWord ++ tailWord_4872823) baseStart_4872823 baseEnd_4872823 := by
    simpa [prefixWord, tailWord_4872823, baseEnd_4872823] using wordTrace_append hprefix tailTrace_4872823
  have hstable : (prefixWord ++ tailWord_4872823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872823).length < 2 ^ (prefixWord ++ tailWord_4872823).sum := by decide
  have hdescent : baseEnd_4872823 < baseStart_4872823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872850 : List Nat := [3, 2, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_4872850 : Nat := 118140960795 + 4872850 * 2 ^ 59
def prefixEnd_4872850 : Nat := 4983230072969 + 3 ^ 40 * 4872850 * 2
def baseEnd_4872850 : Nat := 834038069087121728555059

theorem tailTrace_4872850 : CollatzResearch.WordTrace tailWord_4872850 prefixEnd_4872850 834038069087121728555059 := by
  unfold tailWord_4872850
  simp only [CollatzResearch.WordTrace]
  refine ⟨44431860099126035342242001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118484960264336094245978669 44431860099126035342242001)
  ·
    refine ⟨33323895074344526506681501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44431860099126035342242001 33323895074344526506681501)
    ·
      refine ⟨12496460652879197440005563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33323895074344526506681501 12496460652879197440005563)
      ·
        refine ⟨18744690979318796160008345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12496460652879197440005563 18744690979318796160008345)
        ·
          refine ⟨14058518234489097120006259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18744690979318796160008345 14058518234489097120006259)
          ·
            refine ⟨21087777351733645680009389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14058518234489097120006259 21087777351733645680009389)
            ·
              refine ⟨7907916506900117130003521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21087777351733645680009389 7907916506900117130003521)
              ·
                refine ⟨5930937380175087847502641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7907916506900117130003521 5930937380175087847502641)
                ·
                  refine ⟨4448203035131315885626981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5930937380175087847502641 4448203035131315885626981)
                  ·
                    refine ⟨834038069087121728555059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448203035131315885626981 834038069087121728555059)
                    ·
                      rfl

theorem cell23_4872850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_4872850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872850 prefixEnd_4872850 := by exact prefixLift 4872850
  have htrace : WordTrace (prefixWord ++ tailWord_4872850) baseStart_4872850 baseEnd_4872850 := by
    simpa [prefixWord, tailWord_4872850, baseEnd_4872850] using wordTrace_append hprefix tailTrace_4872850
  have hstable : (prefixWord ++ tailWord_4872850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872850).length < 2 ^ (prefixWord ++ tailWord_4872850).sum := by decide
  have hdescent : baseEnd_4872850 < baseStart_4872850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4872924 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_4872924 : Nat := 118140960795 + 4872924 * 2 ^ 59
def prefixEnd_4872924 : Nat := 4983230072969 + 3 ^ 40 * 4872924 * 2
def baseEnd_4872924 : Nat := 2502152204829797896139837

theorem tailTrace_4872924 : CollatzResearch.WordTrace tailWord_4872924 prefixEnd_4872924 2502152204829797896139837 := by
  unfold tailWord_4872924
  simp only [CollatzResearch.WordTrace]
  refine ⟨88865069699118026003580913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118486759598824034671441217 88865069699118026003580913)
  ·
    refine ⟨66648802274338519502685685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88865069699118026003580913 66648802274338519502685685)
    ·
      refine ⟨6248325213219236203376783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66648802274338519502685685 6248325213219236203376783)
      ·
        refine ⟨9372487819828854305065175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6248325213219236203376783 9372487819828854305065175)
        ·
          refine ⟨14058731729743281457597763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9372487819828854305065175 14058731729743281457597763)
          ·
            refine ⟨21088097594614922186396645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14058731729743281457597763 21088097594614922186396645)
            ·
              refine ⟨3954018298990297909949371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21088097594614922186396645 3954018298990297909949371)
              ·
                refine ⟨5931027448485446864924057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954018298990297909949371 5931027448485446864924057)
                ·
                  refine ⟨4448270586364085148693043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931027448485446864924057 4448270586364085148693043)
                  ·
                    refine ⟨6672405879546127723039565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4448270586364085148693043 6672405879546127723039565)
                    ·
                      refine ⟨2502152204829797896139837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6672405879546127723039565 2502152204829797896139837)
                      ·
                        rfl

theorem cell23_4872924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_4872924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4872924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4872924 prefixEnd_4872924 := by exact prefixLift 4872924
  have htrace : WordTrace (prefixWord ++ tailWord_4872924) baseStart_4872924 baseEnd_4872924 := by
    simpa [prefixWord, tailWord_4872924, baseEnd_4872924] using wordTrace_append hprefix tailTrace_4872924
  have hstable : (prefixWord ++ tailWord_4872924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4872924).length < 2 ^ (prefixWord ++ tailWord_4872924).sum := by decide
  have hdescent : baseEnd_4872924 < baseStart_4872924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4872924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873003 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 4, 4, 2]
def baseStart_4873003 : Nat := 118140960795 + 4873003 * 2 ^ 59
def prefixEnd_4873003 : Nat := 4983230072969 + 3 ^ 40 * 4873003 * 2
def baseEnd_4873003 : Nat := 2502192769801503087051973

theorem tailTrace_4873003 : CollatzResearch.WordTrace tailWord_4873003 prefixEnd_4873003 2502192769801503087051973 := by
  unfold tailWord_4873003
  simp only [CollatzResearch.WordTrace]
  refine ⟨177733020764949848499287663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118488680509966565666191775 177733020764949848499287663)
  ·
    refine ⟨266599531147424772748931495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177733020764949848499287663 266599531147424772748931495)
    ·
      refine ⟨399899296721137159123397243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266599531147424772748931495 399899296721137159123397243)
      ·
        refine ⟨599848945081705738685095865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399899296721137159123397243 599848945081705738685095865)
        ·
          refine ⟨449886708811279304013821899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599848945081705738685095865 449886708811279304013821899)
          ·
            refine ⟨674830063216918956020732849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449886708811279304013821899 674830063216918956020732849)
            ·
              refine ⟨506122547412689217015549637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674830063216918956020732849 506122547412689217015549637)
              ·
                refine ⟨94897977639879228190415557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506122547412689217015549637 94897977639879228190415557)
                ·
                  refine ⟨17793370807477355285702917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94897977639879228190415557 17793370807477355285702917)
                  ·
                    refine ⟨3336257026402004116069297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17793370807477355285702917 3336257026402004116069297)
                    ·
                      refine ⟨2502192769801503087051973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336257026402004116069297 2502192769801503087051973)
                      ·
                        rfl

theorem cell23_4873003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 4, 2].length) (baseStart_4873003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873003 prefixEnd_4873003 := by exact prefixLift 4873003
  have htrace : WordTrace (prefixWord ++ tailWord_4873003) baseStart_4873003 baseEnd_4873003 := by
    simpa [prefixWord, tailWord_4873003, baseEnd_4873003] using wordTrace_append hprefix tailTrace_4873003
  have hstable : (prefixWord ++ tailWord_4873003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873003).length < 2 ^ (prefixWord ++ tailWord_4873003).sum := by decide
  have hdescent : baseEnd_4873003 < baseStart_4873003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873016 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6]
def baseStart_4873016 : Nat := 118140960795 + 4873016 * 2 ^ 59
def prefixEnd_4873016 : Nat := 4983230072969 + 3 ^ 40 * 4873016 * 2
def baseEnd_4873016 : Nat := 2502199445050011536189413

theorem tailTrace_4873016 : CollatzResearch.WordTrace tailWord_4873016 prefixEnd_4873016 2502199445050011536189413 := by
  unfold tailWord_4873016
  simp only [CollatzResearch.WordTrace]
  refine ⟨88866747456951375859755451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118488996609268501146340601 88866747456951375859755451)
  ·
    refine ⟨133300121185427063789633177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88866747456951375859755451 133300121185427063789633177)
    ·
      refine ⟨99975090889070297842224883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133300121185427063789633177 99975090889070297842224883)
      ·
        refine ⟨149962636333605446763337325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99975090889070297842224883 149962636333605446763337325)
        ·
          refine ⟨56235988625102042536251497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149962636333605446763337325 56235988625102042536251497)
          ·
            refine ⟨42176991468826531902188623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56235988625102042536251497 42176991468826531902188623)
            ·
              refine ⟨63265487203239797853282935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42176991468826531902188623 63265487203239797853282935)
              ·
                refine ⟨94898230804859696779924403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63265487203239797853282935 94898230804859696779924403)
                ·
                  refine ⟨142347346207289545169886605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94898230804859696779924403 142347346207289545169886605)
                  ·
                    refine ⟨53380254827733579438707477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142347346207289545169886605 53380254827733579438707477)
                    ·
                      refine ⟨2502199445050011536189413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53380254827733579438707477 2502199445050011536189413)
                      ·
                        rfl

theorem cell23_4873016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_4873016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873016 prefixEnd_4873016 := by exact prefixLift 4873016
  have htrace : WordTrace (prefixWord ++ tailWord_4873016) baseStart_4873016 baseEnd_4873016 := by
    simpa [prefixWord, tailWord_4873016, baseEnd_4873016] using wordTrace_append hprefix tailTrace_4873016
  have hstable : (prefixWord ++ tailWord_4873016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873016).length < 2 ^ (prefixWord ++ tailWord_4873016).sum := by decide
  have hdescent : baseEnd_4873016 < baseStart_4873016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873064 : List Nat := [2, 1, 4, 2, 1, 4, 1, 3, 1, 4]
def baseStart_4873064 : Nat := 118140960795 + 4873064 * 2 ^ 59
def prefixEnd_4873064 : Nat := 4983230072969 + 3 ^ 40 * 4873064 * 2
def baseEnd_4873064 : Nat := 834074697373809116129731

theorem tailTrace_4873064 : CollatzResearch.WordTrace tailWord_4873064 prefixEnd_4873064 834074697373809116129731 := by
  unfold tailWord_4873064
  simp only [CollatzResearch.WordTrace]
  refine ⟨88867622808864427958629123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118490163745152570611505497 88867622808864427958629123)
  ·
    refine ⟨133301434213296641937943685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88867622808864427958629123 133301434213296641937943685)
    ·
      refine ⟨24994018914993120363364441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133301434213296641937943685 24994018914993120363364441)
      ·
        refine ⟨18745514186244840272523331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24994018914993120363364441 18745514186244840272523331)
        ·
          refine ⟨28118271279367260408784997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18745514186244840272523331 28118271279367260408784997)
          ·
            refine ⟨5272175864881361326647187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28118271279367260408784997 5272175864881361326647187)
            ·
              refine ⟨7908263797322041989970781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272175864881361326647187 7908263797322041989970781)
              ·
                refine ⟨2965598923995765746239043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7908263797322041989970781 2965598923995765746239043)
                ·
                  refine ⟨4448398385993648619358565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965598923995765746239043 4448398385993648619358565)
                  ·
                    refine ⟨834074697373809116129731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448398385993648619358565 834074697373809116129731)
                    ·
                      rfl

theorem cell23_4873064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_4873064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873064 prefixEnd_4873064 := by exact prefixLift 4873064
  have htrace : WordTrace (prefixWord ++ tailWord_4873064) baseStart_4873064 baseEnd_4873064 := by
    simpa [prefixWord, tailWord_4873064, baseEnd_4873064] using wordTrace_append hprefix tailTrace_4873064
  have hstable : (prefixWord ++ tailWord_4873064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873064).length < 2 ^ (prefixWord ++ tailWord_4873064).sum := by decide
  have hdescent : baseEnd_4873064 < baseStart_4873064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873087 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 1, 1, 3]
def baseStart_4873087 : Nat := 118140960795 + 4873087 * 2 ^ 59
def prefixEnd_4873087 : Nat := 4983230072969 + 3 ^ 40 * 4873087 * 2
def baseEnd_4873087 : Nat := 2502235902176480758401587

theorem tailTrace_4873087 : CollatzResearch.WordTrace tailWord_4873087 prefixEnd_4873087 2502235902176480758401587 := by
  unfold tailWord_4873087
  simp only [CollatzResearch.WordTrace]
  refine ⟨177736084496645530845345515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118490722997763687230230343 177736084496645530845345515)
  ·
    refine ⟨266604126744968296268018273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177736084496645530845345515 266604126744968296268018273)
    ·
      refine ⟨199953095058726222201013705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266604126744968296268018273 199953095058726222201013705)
      ·
        refine ⟨149964821294044666650760279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199953095058726222201013705 149964821294044666650760279)
        ·
          refine ⟨224947231941066999976140419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149964821294044666650760279 224947231941066999976140419)
          ·
            refine ⟨337420847911600499964210629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224947231941066999976140419 337420847911600499964210629)
            ·
              refine ⟨63266408983425093743289493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 337420847911600499964210629 63266408983425093743289493)
              ·
                refine ⟨2965612921098051269216695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63266408983425093743289493 2965612921098051269216695)
                ·
                  refine ⟨4448419381647076903825043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965612921098051269216695 4448419381647076903825043)
                  ·
                    refine ⟨6672629072470615355737565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4448419381647076903825043 6672629072470615355737565)
                    ·
                      refine ⟨2502235902176480758401587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6672629072470615355737565 2502235902176480758401587)
                      ·
                        rfl

theorem cell23_4873087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 1, 3].length) (baseStart_4873087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873087 prefixEnd_4873087 := by exact prefixLift 4873087
  have htrace : WordTrace (prefixWord ++ tailWord_4873087) baseStart_4873087 baseEnd_4873087 := by
    simpa [prefixWord, tailWord_4873087, baseEnd_4873087] using wordTrace_append hprefix tailTrace_4873087
  have hstable : (prefixWord ++ tailWord_4873087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873087).length < 2 ^ (prefixWord ++ tailWord_4873087).sum := by decide
  have hdescent : baseEnd_4873087 < baseStart_4873087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873114 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2]
def baseStart_4873114 : Nat := 118140960795 + 4873114 * 2 ^ 59
def prefixEnd_4873114 : Nat := 4983230072969 + 3 ^ 40 * 4873114 * 2
def baseEnd_4873114 : Nat := 2502249766154152152763963

theorem tailTrace_4873114 : CollatzResearch.WordTrace tailWord_4873114 prefixEnd_4873114 2502249766154152152763963 := by
  unfold tailWord_4873114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44434267316886928614144599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118491379511698476304385597 44434267316886928614144599)
  ·
    refine ⟨66651400975330392921216899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44434267316886928614144599 66651400975330392921216899)
    ·
      refine ⟨99977101462995589381825349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66651400975330392921216899 99977101462995589381825349)
      ·
        refine ⟨18745706524311673009092253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99977101462995589381825349 18745706524311673009092253)
        ·
          refine ⟨7029639946616877378409595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18745706524311673009092253 7029639946616877378409595)
          ·
            refine ⟨10544459919925316067614393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7029639946616877378409595 10544459919925316067614393)
            ·
              refine ⟨7908344939943987050710795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10544459919925316067614393 7908344939943987050710795)
              ·
                refine ⟨11862517409915980576066193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7908344939943987050710795 11862517409915980576066193)
                ·
                  refine ⟨8896888057436985432049645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11862517409915980576066193 8896888057436985432049645)
                  ·
                    refine ⟨3336333021538869537018617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8896888057436985432049645 3336333021538869537018617)
                    ·
                      refine ⟨2502249766154152152763963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336333021538869537018617 2502249766154152152763963)
                      ·
                        rfl

theorem cell23_4873114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_4873114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873114 prefixEnd_4873114 := by exact prefixLift 4873114
  have htrace : WordTrace (prefixWord ++ tailWord_4873114) baseStart_4873114 baseEnd_4873114 := by
    simpa [prefixWord, tailWord_4873114, baseEnd_4873114] using wordTrace_append hprefix tailTrace_4873114
  have hstable : (prefixWord ++ tailWord_4873114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873114).length < 2 ^ (prefixWord ++ tailWord_4873114).sum := by decide
  have hdescent : baseEnd_4873114 < baseStart_4873114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873123 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4873123 : Nat := 118140960795 + 4873123 * 2 ^ 59
def prefixEnd_4873123 : Nat := 4983230072969 + 3 ^ 40 * 4873123 * 2
def baseEnd_4873123 : Nat := 2502254387480042617551421

theorem tailTrace_4873123 : CollatzResearch.WordTrace tailWord_4873123 prefixEnd_4873123 2502254387480042617551421 := by
  unfold tailWord_4873123
  simp only [CollatzResearch.WordTrace]
  refine ⟨177737397524515108993656023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118491598349676739329104015 177737397524515108993656023)
  ·
    refine ⟨266606096286772663490484035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177737397524515108993656023 266606096286772663490484035)
    ·
      refine ⟨399909144430158995235726053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266606096286772663490484035 399909144430158995235726053)
      ·
        refine ⟨74982964580654811606698635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 399909144430158995235726053 74982964580654811606698635)
        ·
          refine ⟨112474446870982217410047953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74982964580654811606698635 112474446870982217410047953)
          ·
            refine ⟨84355835153236663057535965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112474446870982217410047953 84355835153236663057535965)
            ·
              refine ⟨31633438182463748646575987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84355835153236663057535965 31633438182463748646575987)
              ·
                refine ⟨47450157273695622969863981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31633438182463748646575987 47450157273695622969863981)
                ·
                  refine ⟨17793808977635858613698993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47450157273695622969863981 17793808977635858613698993)
                  ·
                    refine ⟨13345356733226893960274245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17793808977635858613698993 13345356733226893960274245)
                    ·
                      refine ⟨2502254387480042617551421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13345356733226893960274245 2502254387480042617551421)
                      ·
                        rfl

theorem cell23_4873123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4873123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873123 prefixEnd_4873123 := by exact prefixLift 4873123
  have htrace : WordTrace (prefixWord ++ tailWord_4873123) baseStart_4873123 baseEnd_4873123 := by
    simpa [prefixWord, tailWord_4873123, baseEnd_4873123] using wordTrace_append hprefix tailTrace_4873123
  have hstable : (prefixWord ++ tailWord_4873123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873123).length < 2 ^ (prefixWord ++ tailWord_4873123).sum := by decide
  have hdescent : baseEnd_4873123 < baseStart_4873123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873165 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 2, 3, 2]
def baseStart_4873165 : Nat := 118140960795 + 4873165 * 2 ^ 59
def prefixEnd_4873165 : Nat := 4983230072969 + 3 ^ 40 * 4873165 * 2
def baseEnd_4873165 : Nat := 2502275953667531453226229

theorem tailTrace_4873165 : CollatzResearch.WordTrace tailWord_4873165 prefixEnd_4873165 2502275953667531453226229 := by
  unfold tailWord_4873165
  simp only [CollatzResearch.WordTrace]
  refine ⟨177738929390362950166684949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118492619593575300111123299 177738929390362950166684949)
  ·
    refine ⟨8331512315173263289063357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177738929390362950166684949 8331512315173263289063357)
    ·
      refine ⟨3124317118189973733398759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8331512315173263289063357 3124317118189973733398759)
      ·
        refine ⟨4686475677284960600098139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3124317118189973733398759 4686475677284960600098139)
        ·
          refine ⟨7029713515927440900147209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4686475677284960600098139 7029713515927440900147209)
          ·
            refine ⟨5272285136945580675110407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7029713515927440900147209 5272285136945580675110407)
            ·
              refine ⟨7908427705418371012665611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272285136945580675110407 7908427705418371012665611)
              ·
                refine ⟨11862641558127556518998417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7908427705418371012665611 11862641558127556518998417)
                ·
                  refine ⟨8896981168595667389248813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11862641558127556518998417 8896981168595667389248813)
                  ·
                    refine ⟨3336367938223375270968305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8896981168595667389248813 3336367938223375270968305)
                    ·
                      refine ⟨2502275953667531453226229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336367938223375270968305 2502275953667531453226229)
                      ·
                        rfl

theorem cell23_4873165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_4873165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873165 prefixEnd_4873165 := by exact prefixLift 4873165
  have htrace : WordTrace (prefixWord ++ tailWord_4873165) baseStart_4873165 baseEnd_4873165 := by
    simpa [prefixWord, tailWord_4873165, baseEnd_4873165] using wordTrace_append hprefix tailTrace_4873165
  have hstable : (prefixWord ++ tailWord_4873165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873165).length < 2 ^ (prefixWord ++ tailWord_4873165).sum := by decide
  have hdescent : baseEnd_4873165 < baseStart_4873165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873181 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_4873181 : Nat := 118140960795 + 4873181 * 2 ^ 59
def prefixEnd_4873181 : Nat := 4983230072969 + 3 ^ 40 * 4873181 * 2
def baseEnd_4873181 : Nat := 2502284169358003390626155

theorem tailTrace_4873181 : CollatzResearch.WordTrace tailWord_4873181 prefixEnd_4873181 2502284169358003390626155 := by
  unfold tailWord_4873181
  simp only [CollatzResearch.WordTrace]
  refine ⟨177739512958304984899267397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118493008638869989932844931 177739512958304984899267397)
  ·
    refine ⟨33326158679682184668612637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177739512958304984899267397 33326158679682184668612637)
    ·
      refine ⟨12497309504880819250729739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33326158679682184668612637 12497309504880819250729739)
      ·
        refine ⟨18745964257321228876094609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12497309504880819250729739 18745964257321228876094609)
        ·
          refine ⟨14059473192990921657070957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18745964257321228876094609 14059473192990921657070957)
          ·
            refine ⟨5272302447371595621401609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14059473192990921657070957 5272302447371595621401609)
            ·
              refine ⟨3954226835528696716051207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5272302447371595621401609 3954226835528696716051207)
              ·
                refine ⟨5931340253293045074076811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954226835528696716051207 5931340253293045074076811)
                ·
                  refine ⟨8897010379939567611115217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931340253293045074076811 8897010379939567611115217)
                  ·
                    refine ⟨6672757784954675708336413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8897010379939567611115217 6672757784954675708336413)
                    ·
                      refine ⟨2502284169358003390626155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6672757784954675708336413 2502284169358003390626155)
                      ·
                        rfl

theorem cell23_4873181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_4873181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873181 prefixEnd_4873181 := by exact prefixLift 4873181
  have htrace : WordTrace (prefixWord ++ tailWord_4873181) baseStart_4873181 baseEnd_4873181 := by
    simpa [prefixWord, tailWord_4873181, baseEnd_4873181] using wordTrace_append hprefix tailTrace_4873181
  have hstable : (prefixWord ++ tailWord_4873181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873181).length < 2 ^ (prefixWord ++ tailWord_4873181).sum := by decide
  have hdescent : baseEnd_4873181 < baseStart_4873181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873194 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_4873194 : Nat := 118140960795 + 4873194 * 2 ^ 59
def prefixEnd_4873194 : Nat := 4983230072969 + 3 ^ 40 * 4873194 * 2
def baseEnd_4873194 : Nat := 2502290844606511839763595

theorem tailTrace_4873194 : CollatzResearch.WordTrace tailWord_4873194 prefixEnd_4873194 2502290844606511839763595 := by
  unfold tailWord_4873194
  simp only [CollatzResearch.WordTrace]
  refine ⟨44434996776814472029872659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118493324738171925412993757 44434996776814472029872659)
  ·
    refine ⟨66652495165221708044808989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44434996776814472029872659 66652495165221708044808989)
    ·
      refine ⟨24994685686958140516803371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66652495165221708044808989 24994685686958140516803371)
      ·
        refine ⟨37492028530437210775205057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24994685686958140516803371 37492028530437210775205057)
        ·
          refine ⟨28119021397827908081403793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37492028530437210775205057 28119021397827908081403793)
          ·
            refine ⟨21089266048370931061052845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28119021397827908081403793 21089266048370931061052845)
            ·
              refine ⟨7908474768139099147894817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21089266048370931061052845 7908474768139099147894817)
              ·
                refine ⟨5931356076104324360921113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908474768139099147894817 5931356076104324360921113)
                ·
                  refine ⟨4448517057078243270690835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931356076104324360921113 4448517057078243270690835)
                  ·
                    refine ⟨6672775585617364906036253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4448517057078243270690835 6672775585617364906036253)
                    ·
                      refine ⟨2502290844606511839763595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6672775585617364906036253 2502290844606511839763595)
                      ·
                        rfl

theorem cell23_4873194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_4873194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873194 prefixEnd_4873194 := by exact prefixLift 4873194
  have htrace : WordTrace (prefixWord ++ tailWord_4873194) baseStart_4873194 baseEnd_4873194 := by
    simpa [prefixWord, tailWord_4873194, baseEnd_4873194] using wordTrace_append hprefix tailTrace_4873194
  have hstable : (prefixWord ++ tailWord_4873194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873194).length < 2 ^ (prefixWord ++ tailWord_4873194).sum := by decide
  have hdescent : baseEnd_4873194 < baseStart_4873194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873203 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_4873203 : Nat := 118140960795 + 4873203 * 2 ^ 59
def prefixEnd_4873203 : Nat := 4983230072969 + 3 ^ 40 * 4873203 * 2
def baseEnd_4873203 : Nat := 2502295465932402304551053

theorem tailTrace_4873203 : CollatzResearch.WordTrace tailWord_4873203 prefixEnd_4873203 2502295465932402304551053 := by
  unfold tailWord_4873203
  simp only [CollatzResearch.WordTrace]
  refine ⟨177740315364225282656568263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118493543576150188437712175 177740315364225282656568263)
  ·
    refine ⟨266610473046337923984852395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177740315364225282656568263 266610473046337923984852395)
    ·
      refine ⟨399915709569506885977278593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266610473046337923984852395 399915709569506885977278593)
      ·
        refine ⟨299936782177130164482958945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399915709569506885977278593 299936782177130164482958945)
        ·
          refine ⟨224952586632847623362219209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 299936782177130164482958945 224952586632847623362219209)
          ·
            refine ⟨168714439974635717521664407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224952586632847623362219209 168714439974635717521664407)
            ·
              refine ⟨253071659961953576282496611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168714439974635717521664407 253071659961953576282496611)
              ·
                refine ⟨379607489942930364423744917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253071659961953576282496611 379607489942930364423744917)
                ·
                  refine ⟨17794101091074860832363043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 379607489942930364423744917 17794101091074860832363043)
                  ·
                    refine ⟨26691151636612291248544565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17794101091074860832363043 26691151636612291248544565)
                    ·
                      refine ⟨2502295465932402304551053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26691151636612291248544565 2502295465932402304551053)
                      ·
                        rfl

theorem cell23_4873203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_4873203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873203 prefixEnd_4873203 := by exact prefixLift 4873203
  have htrace : WordTrace (prefixWord ++ tailWord_4873203) baseStart_4873203 baseEnd_4873203 := by
    simpa [prefixWord, tailWord_4873203, baseEnd_4873203] using wordTrace_append hprefix tailTrace_4873203
  have hstable : (prefixWord ++ tailWord_4873203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873203).length < 2 ^ (prefixWord ++ tailWord_4873203).sum := by decide
  have hdescent : baseEnd_4873203 < baseStart_4873203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873268 : List Nat := [2, 5, 1, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_4873268 : Nat := 118140960795 + 4873268 * 2 ^ 59
def prefixEnd_4873268 : Nat := 4983230072969 + 3 ^ 40 * 4873268 * 2
def baseEnd_4873268 : Nat := 2502328842174944550238255

theorem tailTrace_4873268 : CollatzResearch.WordTrace tailWord_4873268 prefixEnd_4873268 2502328842174944550238255 := by
  unfold tailWord_4873268
  simp only [CollatzResearch.WordTrace]
  refine ⟨88871343054494899378842229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118495124072659865838456305 88871343054494899378842229)
  ·
    refine ⟨8331688411358896816766459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88871343054494899378842229 8331688411358896816766459)
    ·
      refine ⟨12497532617038345225149689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8331688411358896816766459 12497532617038345225149689)
      ·
        refine ⟨9373149462778758918862267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12497532617038345225149689 9373149462778758918862267)
        ·
          refine ⟨14059724194168138378293401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9373149462778758918862267 14059724194168138378293401)
          ·
            refine ⟨10544793145626103783720051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14059724194168138378293401 10544793145626103783720051)
            ·
              refine ⟨15817189718439155675580077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10544793145626103783720051 15817189718439155675580077)
              ·
                refine ⟨5931446144414683378342529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15817189718439155675580077 5931446144414683378342529)
                ·
                  refine ⟨4448584608311012533756897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931446144414683378342529 4448584608311012533756897)
                  ·
                    refine ⟨3336438456233259400317673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4448584608311012533756897 3336438456233259400317673)
                    ·
                      refine ⟨2502328842174944550238255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336438456233259400317673 2502328842174944550238255)
                      ·
                        rfl

theorem cell23_4873268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_4873268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873268 prefixEnd_4873268 := by exact prefixLift 4873268
  have htrace : WordTrace (prefixWord ++ tailWord_4873268) baseStart_4873268 baseEnd_4873268 := by
    simpa [prefixWord, tailWord_4873268, baseEnd_4873268] using wordTrace_append hprefix tailTrace_4873268
  have hstable : (prefixWord ++ tailWord_4873268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873268).length < 2 ^ (prefixWord ++ tailWord_4873268).sum := by decide
  have hdescent : baseEnd_4873268 < baseStart_4873268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873287 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 2, 5]
def baseStart_4873287 : Nat := 118140960795 + 4873287 * 2 ^ 59
def prefixEnd_4873287 : Nat := 4983230072969 + 3 ^ 40 * 4873287 * 2
def baseEnd_4873287 : Nat := 834112866102459991966889

theorem tailTrace_4873287 : CollatzResearch.WordTrace tailWord_4873287 prefixEnd_4873287 834112866102459991966889 := by
  unfold tailWord_4873287
  simp only [CollatzResearch.WordTrace]
  refine ⟨177743379095920965002626115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118495586063947310001750743 177743379095920965002626115)
  ·
    refine ⟨266615068643881447503939173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177743379095920965002626115 266615068643881447503939173)
    ·
      refine ⟨49990325370727771406988595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266615068643881447503939173 49990325370727771406988595)
      ·
        refine ⟨74985488056091657110482893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49990325370727771406988595 74985488056091657110482893)
        ·
          refine ⟨28119558021034371416431085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74985488056091657110482893 28119558021034371416431085)
          ·
            refine ⟨10544834257887889281161657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28119558021034371416431085 10544834257887889281161657)
            ·
              refine ⟨7908625693415916960871243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10544834257887889281161657 7908625693415916960871243)
              ·
                refine ⟨11862938540123875441306865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7908625693415916960871243 11862938540123875441306865)
                ·
                  refine ⟨8897203905092906580980149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11862938540123875441306865 8897203905092906580980149)
                  ·
                    refine ⟨834112866102459991966889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8897203905092906580980149 834112866102459991966889)
                    ·
                      rfl

theorem cell23_4873287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_4873287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873287 prefixEnd_4873287 := by exact prefixLift 4873287
  have htrace : WordTrace (prefixWord ++ tailWord_4873287) baseStart_4873287 baseEnd_4873287 := by
    simpa [prefixWord, tailWord_4873287, baseEnd_4873287] using wordTrace_append hprefix tailTrace_4873287
  have hstable : (prefixWord ++ tailWord_4873287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873287).length < 2 ^ (prefixWord ++ tailWord_4873287).sum := by decide
  have hdescent : baseEnd_4873287 < baseStart_4873287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873290 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4]
def baseStart_4873290 : Nat := 118140960795 + 4873290 * 2 ^ 59
def prefixEnd_4873290 : Nat := 4983230072969 + 3 ^ 40 * 4873290 * 2
def baseEnd_4873290 : Nat := 2502340138749343464163153

theorem tailTrace_4873290 : CollatzResearch.WordTrace tailWord_4873290 prefixEnd_4873290 2502340138749343464163153 := by
  unfold tailWord_4873290
  simp only [CollatzResearch.WordTrace]
  refine ⟨44435872128727524128746331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118495659009940064343323549 44435872128727524128746331)
  ·
    refine ⟨66653808193091286193119497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44435872128727524128746331 66653808193091286193119497)
    ·
      refine ⟨49990356144818464644839623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66653808193091286193119497 49990356144818464644839623)
      ·
        refine ⟨74985534217227696967259435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49990356144818464644839623 74985534217227696967259435)
        ·
          refine ⟨112478301325841545450889153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74985534217227696967259435 112478301325841545450889153)
          ·
            refine ⟨84358725994381159088166865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112478301325841545450889153 84358725994381159088166865)
            ·
              refine ⟨63269044495785869316125149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84358725994381159088166865 63269044495785869316125149)
              ·
                refine ⟨23725891685919700993546931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63269044495785869316125149 23725891685919700993546931)
                ·
                  refine ⟨35588837528879551490320397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23725891685919700993546931 35588837528879551490320397)
                  ·
                    refine ⟨13345814073329831808870149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35588837528879551490320397 13345814073329831808870149)
                    ·
                      refine ⟨2502340138749343464163153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13345814073329831808870149 2502340138749343464163153)
                      ·
                        rfl

theorem cell23_4873290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_4873290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873290 prefixEnd_4873290 := by exact prefixLift 4873290
  have htrace : WordTrace (prefixWord ++ tailWord_4873290) baseStart_4873290 baseEnd_4873290 := by
    simpa [prefixWord, tailWord_4873290, baseEnd_4873290] using wordTrace_append hprefix tailTrace_4873290
  have hstable : (prefixWord ++ tailWord_4873290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873290).length < 2 ^ (prefixWord ++ tailWord_4873290).sum := by decide
  have hdescent : baseEnd_4873290 < baseStart_4873290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873317 : List Nat := [1, 3, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_4873317 : Nat := 118140960795 + 4873317 * 2 ^ 59
def prefixEnd_4873317 : Nat := 4983230072969 + 3 ^ 40 * 4873317 * 2
def baseEnd_4873317 : Nat := 834118000909004952841843

theorem tailTrace_4873317 : CollatzResearch.WordTrace tailWord_4873317 prefixEnd_4873317 834118000909004952841843 := by
  unfold tailWord_4873317
  simp only [CollatzResearch.WordTrace]
  refine ⟨177744473285812280126218205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118496315523874853417478803 177744473285812280126218205)
  ·
    refine ⟨66654177482179605047331827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177744473285812280126218205 66654177482179605047331827)
    ·
      refine ⟨99981266223269407570997741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66654177482179605047331827 99981266223269407570997741)
      ·
        refine ⟨37492974833726027839124153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99981266223269407570997741 37492974833726027839124153)
        ·
          refine ⟨28119731125294520879343115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37492974833726027839124153 28119731125294520879343115)
          ·
            refine ⟨42179596687941781319014673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28119731125294520879343115 42179596687941781319014673)
            ·
              refine ⟨31634697515956335989261005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42179596687941781319014673 31634697515956335989261005)
              ·
                refine ⟨11863011568483625995972877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31634697515956335989261005 11863011568483625995972877)
                ·
                  refine ⟨4448629338181359748489829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11863011568483625995972877 4448629338181359748489829)
                  ·
                    refine ⟨834118000909004952841843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448629338181359748489829 834118000909004952841843)
                    ·
                      rfl

theorem cell23_4873317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_4873317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873317 prefixEnd_4873317 := by exact prefixLift 4873317
  have htrace : WordTrace (prefixWord ++ tailWord_4873317) baseStart_4873317 baseEnd_4873317 := by
    simpa [prefixWord, tailWord_4873317, baseEnd_4873317] using wordTrace_append hprefix tailTrace_4873317
  have hstable : (prefixWord ++ tailWord_4873317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873317).length < 2 ^ (prefixWord ++ tailWord_4873317).sum := by decide
  have hdescent : baseEnd_4873317 < baseStart_4873317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873334 : List Nat := [5, 1, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_4873334 : Nat := 118140960795 + 4873334 * 2 ^ 59
def prefixEnd_4873334 : Nat := 4983230072969 + 3 ^ 40 * 4873334 * 2
def baseEnd_4873334 : Nat := 834120910632713764004317

theorem tailTrace_4873334 : CollatzResearch.WordTrace tailWord_4873334 prefixEnd_4873334 834120910632713764004317 := by
  unfold tailWord_4873334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11109068332921918251849191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118496728884500461353058037 11109068332921918251849191)
  ·
    refine ⟨16663602499382877377773787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11109068332921918251849191 16663602499382877377773787)
    ·
      refine ⟨24995403749074316066660681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16663602499382877377773787 24995403749074316066660681)
      ·
        refine ⟨18746552811805737049995511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24995403749074316066660681 18746552811805737049995511)
        ·
          refine ⟨28119829217708605574993267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18746552811805737049995511 28119829217708605574993267)
          ·
            refine ⟨42179743826562908362489901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28119829217708605574993267 42179743826562908362489901)
            ·
              refine ⟨15817403934961090635933713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42179743826562908362489901 15817403934961090635933713)
              ·
                refine ⟨11863052951220817976950285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15817403934961090635933713 11863052951220817976950285)
                ·
                  refine ⟨4448644856707806741356357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11863052951220817976950285 4448644856707806741356357)
                  ·
                    refine ⟨834120910632713764004317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448644856707806741356357 834120910632713764004317)
                    ·
                      rfl

theorem cell23_4873334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_4873334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873334 prefixEnd_4873334 := by exact prefixLift 4873334
  have htrace : WordTrace (prefixWord ++ tailWord_4873334) baseStart_4873334 baseEnd_4873334 := by
    simpa [prefixWord, tailWord_4873334, baseEnd_4873334] using wordTrace_append hprefix tailTrace_4873334
  have hstable : (prefixWord ++ tailWord_4873334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873334).length < 2 ^ (prefixWord ++ tailWord_4873334).sum := by decide
  have hdescent : baseEnd_4873334 < baseStart_4873334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873360 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 5, 5]
def baseStart_4873360 : Nat := 118140960795 + 4873360 * 2 ^ 59
def prefixEnd_4873360 : Nat := 4983230072969 + 3 ^ 40 * 4873360 * 2
def baseEnd_4873360 : Nat := 834125360798386063429277

theorem tailTrace_4873360 : CollatzResearch.WordTrace tailWord_4873360 prefixEnd_4873360 834125360798386063429277 := by
  unfold tailWord_4873360
  simp only [CollatzResearch.WordTrace]
  refine ⟨88873020812328249235016767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118497361083104332313355689 88873020812328249235016767)
  ·
    refine ⟨133309531218492373852525151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88873020812328249235016767 133309531218492373852525151)
    ·
      refine ⟨199964296827738560778787727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133309531218492373852525151 199964296827738560778787727)
      ·
        refine ⟨299946445241607841168181591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199964296827738560778787727 299946445241607841168181591)
        ·
          refine ⟨449919667862411761752272387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299946445241607841168181591 449919667862411761752272387)
          ·
            refine ⟨674879501793617642628408581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449919667862411761752272387 674879501793617642628408581)
            ·
              refine ⟨126539906586303307992826609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 674879501793617642628408581 126539906586303307992826609)
              ·
                refine ⟨94904929939727480994619957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126539906586303307992826609 94904929939727480994619957)
                ·
                  refine ⟨8897337181849451343245621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94904929939727480994619957 8897337181849451343245621)
                  ·
                    refine ⟨834125360798386063429277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8897337181849451343245621 834125360798386063429277)
                    ·
                      rfl

theorem cell23_4873360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 5, 5].length) (baseStart_4873360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873360 prefixEnd_4873360 := by exact prefixLift 4873360
  have htrace : WordTrace (prefixWord ++ tailWord_4873360) baseStart_4873360 baseEnd_4873360 := by
    simpa [prefixWord, tailWord_4873360, baseEnd_4873360] using wordTrace_append hprefix tailTrace_4873360
  have hstable : (prefixWord ++ tailWord_4873360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873360).length < 2 ^ (prefixWord ++ tailWord_4873360).sum := by decide
  have hdescent : baseEnd_4873360 < baseStart_4873360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873394 : List Nat := [3, 2, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_4873394 : Nat := 118140960795 + 4873394 * 2 ^ 59
def prefixEnd_4873394 : Nat := 4983230072969 + 3 ^ 40 * 4873394 * 2
def baseEnd_4873394 : Nat := 834131180245803685754225

theorem tailTrace_4873394 : CollatzResearch.WordTrace tailWord_4873394 prefixEnd_4873394 834131180245803685754225 := by
  unfold tailWord_4873394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44436820426633330569192809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118498187804355548184514157 44436820426633330569192809)
  ·
    refine ⟨33327615319974997926894607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44436820426633330569192809 33327615319974997926894607)
    ·
      refine ⟨49991422979962496890341911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33327615319974997926894607 49991422979962496890341911)
      ·
        refine ⟨74987134469943745335512867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49991422979962496890341911 74987134469943745335512867)
        ·
          refine ⟨112480701704915618003269301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74987134469943745335512867 112480701704915618003269301)
          ·
            refine ⟨10545065784835839187806497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112480701704915618003269301 10545065784835839187806497)
            ·
              refine ⟨7908799338626879390854873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10545065784835839187806497 7908799338626879390854873)
              ·
                refine ⟨5931599503970159543141155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908799338626879390854873 5931599503970159543141155)
                ·
                  refine ⟨8897399255955239314711733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931599503970159543141155 8897399255955239314711733)
                  ·
                    refine ⟨834131180245803685754225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8897399255955239314711733 834131180245803685754225)
                    ·
                      rfl

theorem cell23_4873394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_4873394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873394 prefixEnd_4873394 := by exact prefixLift 4873394
  have htrace : WordTrace (prefixWord ++ tailWord_4873394) baseStart_4873394 baseEnd_4873394 := by
    simpa [prefixWord, tailWord_4873394, baseEnd_4873394] using wordTrace_append hprefix tailTrace_4873394
  have hstable : (prefixWord ++ tailWord_4873394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873394).length < 2 ^ (prefixWord ++ tailWord_4873394).sum := by decide
  have hdescent : baseEnd_4873394 < baseStart_4873394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873407 : List Nat := [1, 1, 2, 2, 2, 2, 3, 2, 4, 4]
def baseStart_4873407 : Nat := 118140960795 + 4873407 * 2 ^ 59
def prefixEnd_4873407 : Nat := 4983230072969 + 3 ^ 40 * 4873407 * 2
def baseEnd_4873407 : Nat := 834133405328639835466705

theorem tailTrace_4873407 : CollatzResearch.WordTrace tailWord_4873407 prefixEnd_4873407 834133405328639835466705 := by
  unfold tailWord_4873407
  simp only [CollatzResearch.WordTrace]
  refine ⟨177747755855486225496994475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118498503903657483664662983 177747755855486225496994475)
  ·
    refine ⟨266621633783229338245491713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177747755855486225496994475 266621633783229338245491713)
    ·
      refine ⟨199966225337422003684118785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266621633783229338245491713 199966225337422003684118785)
      ·
        refine ⟨149974669003066502763089089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199966225337422003684118785 149974669003066502763089089)
        ·
          refine ⟨112481001752299877072316817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149974669003066502763089089 112481001752299877072316817)
          ·
            refine ⟨84360751314224907804237613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112481001752299877072316817 84360751314224907804237613)
            ·
              refine ⟨31635281742834340426589105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84360751314224907804237613 31635281742834340426589105)
              ·
                refine ⟨23726461307125755319941829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31635281742834340426589105 23726461307125755319941829)
                ·
                  refine ⟨4448711495086079122489093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23726461307125755319941829 4448711495086079122489093)
                  ·
                    refine ⟨834133405328639835466705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448711495086079122489093 834133405328639835466705)
                    ·
                      rfl

theorem cell23_4873407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_4873407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873407 prefixEnd_4873407 := by exact prefixLift 4873407
  have htrace : WordTrace (prefixWord ++ tailWord_4873407) baseStart_4873407 baseEnd_4873407 := by
    simpa [prefixWord, tailWord_4873407, baseEnd_4873407] using wordTrace_append hprefix tailTrace_4873407
  have hstable : (prefixWord ++ tailWord_4873407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873407).length < 2 ^ (prefixWord ++ tailWord_4873407).sum := by decide
  have hdescent : baseEnd_4873407 < baseStart_4873407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873431 : List Nat := [1, 1, 3, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_4873431 : Nat := 118140960795 + 4873431 * 2 ^ 59
def prefixEnd_4873431 : Nat := 4983230072969 + 3 ^ 40 * 4873431 * 2
def baseEnd_4873431 : Nat := 2502412539521627412500005

theorem tailTrace_4873431 : CollatzResearch.WordTrace tailWord_4873431 prefixEnd_4873431 2502412539521627412500005 := by
  unfold tailWord_4873431
  simp only [CollatzResearch.WordTrace]
  refine ⟨177748631207399277595868147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118499087471599518397245431 177748631207399277595868147)
  ·
    refine ⟨266622946811098916393802221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177748631207399277595868147 266622946811098916393802221)
    ·
      refine ⟨99983605054162093647675833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266622946811098916393802221 99983605054162093647675833)
      ·
        refine ⟨74987703790621570235756875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99983605054162093647675833 74987703790621570235756875)
        ·
          refine ⟨112481555685932355353635313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74987703790621570235756875 112481555685932355353635313)
          ·
            refine ⟨84361166764449266515226485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112481555685932355353635313 84361166764449266515226485)
            ·
              refine ⟨7908859384167118735802483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84361166764449266515226485 7908859384167118735802483)
              ·
                refine ⟨11863289076250678103703725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7908859384167118735802483 11863289076250678103703725)
                ·
                  refine ⟨4448733403594004288888897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11863289076250678103703725 4448733403594004288888897)
                  ·
                    refine ⟨3336550052695503216666673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4448733403594004288888897 3336550052695503216666673)
                    ·
                      refine ⟨2502412539521627412500005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336550052695503216666673 2502412539521627412500005)
                      ·
                        rfl

theorem cell23_4873431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_4873431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873431 prefixEnd_4873431 := by exact prefixLift 4873431
  have htrace : WordTrace (prefixWord ++ tailWord_4873431) baseStart_4873431 baseEnd_4873431 := by
    simpa [prefixWord, tailWord_4873431, baseEnd_4873431] using wordTrace_append hprefix tailTrace_4873431
  have hstable : (prefixWord ++ tailWord_4873431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873431).length < 2 ^ (prefixWord ++ tailWord_4873431).sum := by decide
  have hdescent : baseEnd_4873431 < baseStart_4873431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873441 : List Nat := [1, 2, 3, 1, 3, 2, 4, 1, 2, 4]
def baseStart_4873441 : Nat := 118140960795 + 4873441 * 2 ^ 59
def prefixEnd_4873441 : Nat := 4983230072969 + 3 ^ 40 * 4873441 * 2
def baseEnd_4873441 : Nat := 834139224776057457791653

theorem tailTrace_4873441 : CollatzResearch.WordTrace tailWord_4873441 prefixEnd_4873441 834139224776057457791653 := by
  unfold tailWord_4873441
  simp only [CollatzResearch.WordTrace]
  refine ⟨177748995937363049303732177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118499330624908699535821451 177748995937363049303732177)
  ·
    refine ⟨133311746953022286977799133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177748995937363049303732177 133311746953022286977799133)
    ·
      refine ⟨49991905107383357616674675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133311746953022286977799133 49991905107383357616674675)
      ·
        refine ⟨74987857661075036425012013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49991905107383357616674675 74987857661075036425012013)
        ·
          refine ⟨28120446622903138659379505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74987857661075036425012013 28120446622903138659379505)
          ·
            refine ⟨21090334967177353994534629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28120446622903138659379505 21090334967177353994534629)
            ·
              refine ⟨3954437806345753873975243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21090334967177353994534629 3954437806345753873975243)
              ·
                refine ⟨5931656709518630810962865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954437806345753873975243 5931656709518630810962865)
                ·
                  refine ⟨4448742532138973108222149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931656709518630810962865 4448742532138973108222149)
                  ·
                    refine ⟨834139224776057457791653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4448742532138973108222149 834139224776057457791653)
                    ·
                      rfl

theorem cell23_4873441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_4873441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873441 prefixEnd_4873441 := by exact prefixLift 4873441
  have htrace : WordTrace (prefixWord ++ tailWord_4873441) baseStart_4873441 baseEnd_4873441 := by
    simpa [prefixWord, tailWord_4873441, baseEnd_4873441] using wordTrace_append hprefix tailTrace_4873441
  have hstable : (prefixWord ++ tailWord_4873441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873441).length < 2 ^ (prefixWord ++ tailWord_4873441).sum := by decide
  have hdescent : baseEnd_4873441 < baseStart_4873441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873451 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 3]
def baseStart_4873451 : Nat := 118140960795 + 4873451 * 2 ^ 59
def prefixEnd_4873451 : Nat := 4983230072969 + 3 ^ 40 * 4873451 * 2
def baseEnd_4873451 : Nat := 2502422809134717334249913

theorem tailTrace_4873451 : CollatzResearch.WordTrace tailWord_4873451 prefixEnd_4873451 2502422809134717334249913 := by
  unfold tailWord_4873451
  simp only [CollatzResearch.WordTrace]
  refine ⟨177749360667326821011596207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118499573778217880674397471 177749360667326821011596207)
  ·
    refine ⟨266624041000990231517394311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177749360667326821011596207 266624041000990231517394311)
    ·
      refine ⟨399936061501485347276091467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266624041000990231517394311 399936061501485347276091467)
      ·
        refine ⟨599904092252228020914137201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399936061501485347276091467 599904092252228020914137201)
        ·
          refine ⟨449928069189171015685602901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599904092252228020914137201 449928069189171015685602901)
          ·
            refine ⟨5272594560810597840065659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 449928069189171015685602901 5272594560810597840065659)
            ·
              refine ⟨7908891841215896760098489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5272594560810597840065659 7908891841215896760098489)
              ·
                refine ⟨5931668880911922570073867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908891841215896760098489 5931668880911922570073867)
                ·
                  refine ⟨8897503321367883855110801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931668880911922570073867 8897503321367883855110801)
                  ·
                    refine ⟨6673127491025912891333101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8897503321367883855110801 6673127491025912891333101)
                    ·
                      refine ⟨2502422809134717334249913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673127491025912891333101 2502422809134717334249913)
                      ·
                        rfl

theorem cell23_4873451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 2, 3].length) (baseStart_4873451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873451 prefixEnd_4873451 := by exact prefixLift 4873451
  have htrace : WordTrace (prefixWord ++ tailWord_4873451) baseStart_4873451 baseEnd_4873451 := by
    simpa [prefixWord, tailWord_4873451, baseEnd_4873451] using wordTrace_append hprefix tailTrace_4873451
  have hstable : (prefixWord ++ tailWord_4873451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873451).length < 2 ^ (prefixWord ++ tailWord_4873451).sum := by decide
  have hdescent : baseEnd_4873451 < baseStart_4873451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873468 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_4873468 : Nat := 118140960795 + 4873468 * 2 ^ 59
def prefixEnd_4873468 : Nat := 4983230072969 + 3 ^ 40 * 4873468 * 2
def baseEnd_4873468 : Nat := 2502431538305843767737335

theorem tailTrace_4873468 : CollatzResearch.WordTrace tailWord_4873468 prefixEnd_4873468 2502431538305843767737335 := by
  unfold tailWord_4873468
  simp only [CollatzResearch.WordTrace]
  refine ⟨88874990354132616457482529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118499987138843488609976705 88874990354132616457482529)
  ·
    refine ⟨66656242765599462343111897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88874990354132616457482529 66656242765599462343111897)
    ·
      refine ⟨49992182074199596757333923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66656242765599462343111897 49992182074199596757333923)
      ·
        refine ⟨74988273111299395136000885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49992182074199596757333923 74988273111299395136000885)
        ·
          refine ⟨7030150604184318294000083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74988273111299395136000885 7030150604184318294000083)
          ·
            refine ⟨10545225906276477441000125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030150604184318294000083 10545225906276477441000125)
            ·
              refine ⟨3954459714853679040375047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10545225906276477441000125 3954459714853679040375047)
              ·
                refine ⟨5931689572280518560562571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954459714853679040375047 5931689572280518560562571)
                ·
                  refine ⟨8897534358420777840843857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931689572280518560562571 8897534358420777840843857)
                  ·
                    refine ⟨6673150768815583380632893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8897534358420777840843857 6673150768815583380632893)
                    ·
                      refine ⟨2502431538305843767737335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673150768815583380632893 2502431538305843767737335)
                      ·
                        rfl

theorem cell23_4873468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_4873468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873468 prefixEnd_4873468 := by exact prefixLift 4873468
  have htrace : WordTrace (prefixWord ++ tailWord_4873468) baseStart_4873468 baseEnd_4873468 := by
    simpa [prefixWord, tailWord_4873468, baseEnd_4873468] using wordTrace_append hprefix tailTrace_4873468
  have hstable : (prefixWord ++ tailWord_4873468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873468).length < 2 ^ (prefixWord ++ tailWord_4873468).sum := by decide
  have hdescent : baseEnd_4873468 < baseStart_4873468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873481 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 3]
def baseStart_4873481 : Nat := 118140960795 + 4873481 * 2 ^ 59
def prefixEnd_4873481 : Nat := 4983230072969 + 3 ^ 40 * 4873481 * 2
def baseEnd_4873481 : Nat := 2502438213554352216874775

theorem tailTrace_4873481 : CollatzResearch.WordTrace tailWord_4873481 prefixEnd_4873481 2502438213554352216874775 := by
  unfold tailWord_4873481
  simp only [CollatzResearch.WordTrace]
  refine ⟨177750454857218136135188297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118500303238145424090125531 177750454857218136135188297)
  ·
    refine ⟨133312841142913602101391223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177750454857218136135188297 133312841142913602101391223)
    ·
      refine ⟨199969261714370403152086835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133312841142913602101391223 199969261714370403152086835)
      ·
        refine ⟨299953892571555604728130253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199969261714370403152086835 299953892571555604728130253)
        ·
          refine ⟨112482709714333351773048845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299953892571555604728130253 112482709714333351773048845)
          ·
            refine ⟨42181016142875006914893317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112482709714333351773048845 42181016142875006914893317)
            ·
              refine ⟨7908940526789063796542497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42181016142875006914893317 7908940526789063796542497)
              ·
                refine ⟨5931705395091797847406873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7908940526789063796542497 5931705395091797847406873)
                ·
                  refine ⟨4448779046318848385555155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5931705395091797847406873 4448779046318848385555155)
                  ·
                    refine ⟨6673168569478272578332733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4448779046318848385555155 6673168569478272578332733)
                    ·
                      refine ⟨2502438213554352216874775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673168569478272578332733 2502438213554352216874775)
                      ·
                        rfl

theorem cell23_4873481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 1, 3].length) (baseStart_4873481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873481 prefixEnd_4873481 := by exact prefixLift 4873481
  have htrace : WordTrace (prefixWord ++ tailWord_4873481) baseStart_4873481 baseEnd_4873481 := by
    simpa [prefixWord, tailWord_4873481, baseEnd_4873481] using wordTrace_append hprefix tailTrace_4873481
  have hstable : (prefixWord ++ tailWord_4873481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873481).length < 2 ^ (prefixWord ++ tailWord_4873481).sum := by decide
  have hdescent : baseEnd_4873481 < baseStart_4873481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873521 : List Nat := [1, 2, 2, 3, 3, 1, 2, 2, 1, 4, 2]
def baseStart_4873521 : Nat := 118140960795 + 4873521 * 2 ^ 59
def prefixEnd_4873521 : Nat := 4983230072969 + 3 ^ 40 * 4873521 * 2
def baseEnd_4873521 : Nat := 2502458752780532060374591

theorem tailTrace_4873521 : CollatzResearch.WordTrace tailWord_4873521 prefixEnd_4873521 2502458752780532060374591 := by
  unfold tailWord_4873521
  simp only [CollatzResearch.WordTrace]
  refine ⟨177751913777073222966644417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118501275851382148644429611 177751913777073222966644417)
  ·
    refine ⟨133313935332804917224983313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177751913777073222966644417 133313935332804917224983313)
    ·
      refine ⟨99985451499603687918737485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133313935332804917224983313 99985451499603687918737485)
      ·
        refine ⟨37494544312351382969526557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99985451499603687918737485 37494544312351382969526557)
        ·
          refine ⟨14060454117131768613572459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37494544312351382969526557 14060454117131768613572459)
          ·
            refine ⟨21090681175697652920358689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14060454117131768613572459 21090681175697652920358689)
            ·
              refine ⟨15818010881773239690269017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21090681175697652920358689 15818010881773239690269017)
              ·
                refine ⟨11863508161329929767701763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15818010881773239690269017 11863508161329929767701763)
                ·
                  refine ⟨17795262241994894651552645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11863508161329929767701763 17795262241994894651552645)
                  ·
                    refine ⟨3336611670374042747166121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17795262241994894651552645 3336611670374042747166121)
                    ·
                      refine ⟨2502458752780532060374591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336611670374042747166121 2502458752780532060374591)
                      ·
                        rfl

theorem cell23_4873521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 4, 2].length) (baseStart_4873521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873521 prefixEnd_4873521 := by exact prefixLift 4873521
  have htrace : WordTrace (prefixWord ++ tailWord_4873521) baseStart_4873521 baseEnd_4873521 := by
    simpa [prefixWord, tailWord_4873521, baseEnd_4873521] using wordTrace_append hprefix tailTrace_4873521
  have hstable : (prefixWord ++ tailWord_4873521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873521).length < 2 ^ (prefixWord ++ tailWord_4873521).sum := by decide
  have hdescent : baseEnd_4873521 < baseStart_4873521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873524 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_4873524 : Nat := 118140960795 + 4873524 * 2 ^ 59
def prefixEnd_4873524 : Nat := 4983230072969 + 3 ^ 40 * 4873524 * 2
def baseEnd_4873524 : Nat := 2502460293222495548637077

theorem tailTrace_4873524 : CollatzResearch.WordTrace tailWord_4873524 prefixEnd_4873524 2502460293222495548637077 := by
  unfold tailWord_4873524
  simp only [CollatzResearch.WordTrace]
  refine ⟨88876011598031177239501813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118501348797374902986002417 88876011598031177239501813)
  ·
    refine ⟨8332126087315422866203295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88876011598031177239501813 8332126087315422866203295)
    ·
      refine ⟨12498189130973134299304943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8332126087315422866203295 12498189130973134299304943)
      ·
        refine ⟨18747283696459701448957415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12498189130973134299304943 18747283696459701448957415)
        ·
          refine ⟨28120925544689552173436123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18747283696459701448957415 28120925544689552173436123)
          ·
            refine ⟨42181388317034328260154185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28120925544689552173436123 42181388317034328260154185)
            ·
              refine ⟨31636041237775746195115639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42181388317034328260154185 31636041237775746195115639)
              ·
                refine ⟨47454061856663619292673459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31636041237775746195115639 47454061856663619292673459)
                ·
                  refine ⟨71181092784995428939010189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47454061856663619292673459 71181092784995428939010189)
                  ·
                    refine ⟨26692909794373285852128821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71181092784995428939010189 26692909794373285852128821)
                    ·
                      refine ⟨2502460293222495548637077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26692909794373285852128821 2502460293222495548637077)
                      ·
                        rfl

theorem cell23_4873524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_4873524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873524 prefixEnd_4873524 := by exact prefixLift 4873524
  have htrace : WordTrace (prefixWord ++ tailWord_4873524) baseStart_4873524 baseEnd_4873524 := by
    simpa [prefixWord, tailWord_4873524, baseEnd_4873524] using wordTrace_append hprefix tailTrace_4873524
  have hstable : (prefixWord ++ tailWord_4873524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873524).length < 2 ^ (prefixWord ++ tailWord_4873524).sum := by decide
  have hdescent : baseEnd_4873524 < baseStart_4873524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873525 : List Nat := [1, 3, 3, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_4873525 : Nat := 118140960795 + 4873525 * 2 ^ 59
def prefixEnd_4873525 : Nat := 4983230072969 + 3 ^ 40 * 4873525 * 2
def baseEnd_4873525 : Nat := 2502460806703150044724573

theorem tailTrace_4873525 : CollatzResearch.WordTrace tailWord_4873525 prefixEnd_4873525 2502460806703150044724573 := by
  unfold tailWord_4873525
  simp only [CollatzResearch.WordTrace]
  refine ⟨177752059669058731649790029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118501373112705821099860019 177752059669058731649790029)
  ·
    refine ⟨66657022375897024368671261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177752059669058731649790029 66657022375897024368671261)
    ·
      refine ⟨24996383390961384138251723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66657022375897024368671261 24996383390961384138251723)
      ·
        refine ⟨37494575086442076207377585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24996383390961384138251723 37494575086442076207377585)
        ·
          refine ⟨28120931314831557155533189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37494575086442076207377585 28120931314831557155533189)
          ·
            refine ⟨5272674621530916966662473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28120931314831557155533189 5272674621530916966662473)
            ·
              refine ⟨3954505966148187724996855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5272674621530916966662473 3954505966148187724996855)
              ·
                refine ⟨5931758949222281587495283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954505966148187724996855 5931758949222281587495283)
                ·
                  refine ⟨8897638423833422381242925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5931758949222281587495283 8897638423833422381242925)
                  ·
                    refine ⟨3336614408937533392966097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8897638423833422381242925 3336614408937533392966097)
                    ·
                      refine ⟨2502460806703150044724573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336614408937533392966097 2502460806703150044724573)
                      ·
                        rfl

theorem cell23_4873525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_4873525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873525 prefixEnd_4873525 := by exact prefixLift 4873525
  have htrace : WordTrace (prefixWord ++ tailWord_4873525) baseStart_4873525 baseEnd_4873525 := by
    simpa [prefixWord, tailWord_4873525, baseEnd_4873525] using wordTrace_append hprefix tailTrace_4873525
  have hstable : (prefixWord ++ tailWord_4873525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873525).length < 2 ^ (prefixWord ++ tailWord_4873525).sum := by decide
  have hdescent : baseEnd_4873525 < baseStart_4873525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873534 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4873534 : Nat := 118140960795 + 4873534 * 2 ^ 59
def prefixEnd_4873534 : Nat := 4983230072969 + 3 ^ 40 * 4873534 * 2
def baseEnd_4873534 : Nat := 2502465428029040509512031

theorem tailTrace_4873534 : CollatzResearch.WordTrace tailWord_4873534 prefixEnd_4873534 2502465428029040509512031 := by
  unfold tailWord_4873534
  simp only [CollatzResearch.WordTrace]
  refine ⟨22219048490753265773358457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118501591950684084124578437 22219048490753265773358457)
  ·
    refine ⟨16664286368064949330018843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22219048490753265773358457 16664286368064949330018843)
    ·
      refine ⟨24996429552097423995028265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16664286368064949330018843 24996429552097423995028265)
      ·
        refine ⟨18747322164073067996271199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24996429552097423995028265 18747322164073067996271199)
        ·
          refine ⟨28120983246109601994406799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18747322164073067996271199 28120983246109601994406799)
          ·
            refine ⟨42181474869164402991610199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28120983246109601994406799 42181474869164402991610199)
            ·
              refine ⟨63272212303746604487415299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42181474869164402991610199 63272212303746604487415299)
              ·
                refine ⟨94908318455619906731122949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63272212303746604487415299 94908318455619906731122949)
                ·
                  refine ⟨17795309710428732512085553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94908318455619906731122949 17795309710428732512085553)
                  ·
                    refine ⟨13346482282821549384064165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17795309710428732512085553 13346482282821549384064165)
                    ·
                      refine ⟨2502465428029040509512031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13346482282821549384064165 2502465428029040509512031)
                      ·
                        rfl

theorem cell23_4873534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4873534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873534 prefixEnd_4873534 := by exact prefixLift 4873534
  have htrace : WordTrace (prefixWord ++ tailWord_4873534) baseStart_4873534 baseEnd_4873534 := by
    simpa [prefixWord, tailWord_4873534, baseEnd_4873534] using wordTrace_append hprefix tailTrace_4873534
  have hstable : (prefixWord ++ tailWord_4873534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873534).length < 2 ^ (prefixWord ++ tailWord_4873534).sum := by decide
  have hdescent : baseEnd_4873534 < baseStart_4873534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873567 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5]
def baseStart_4873567 : Nat := 118140960795 + 4873567 * 2 ^ 59
def prefixEnd_4873567 : Nat := 4983230072969 + 3 ^ 40 * 4873567 * 2
def baseEnd_4873567 : Nat := 2502482372890638880399379

theorem tailTrace_4873567 : CollatzResearch.WordTrace tailWord_4873567 prefixEnd_4873567 2502482372890638880399379 := by
  unfold tailWord_4873567
  simp only [CollatzResearch.WordTrace]
  refine ⟨177753591534906572822818955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118502394356604381881879303 177753591534906572822818955)
  ·
    refine ⟨266630387302359859234228433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177753591534906572822818955 266630387302359859234228433)
    ·
      refine ⟨199972790476769894425671325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266630387302359859234228433 199972790476769894425671325)
      ·
        refine ⟨74989796428788710409626747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199972790476769894425671325 74989796428788710409626747)
        ·
          refine ⟨112484694643183065614440121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74989796428788710409626747 112484694643183065614440121)
          ·
            refine ⟨84363520982387299210830091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112484694643183065614440121 84363520982387299210830091)
            ·
              refine ⟨126545281473580948816245137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84363520982387299210830091 126545281473580948816245137)
              ·
                refine ⟨94908961105185711612183853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126545281473580948816245137 94908961105185711612183853)
                ·
                  refine ⟨35590860414444641854568945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94908961105185711612183853 35590860414444641854568945)
                  ·
                    refine ⟨26693145310833481390926709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35590860414444641854568945 26693145310833481390926709)
                    ·
                      refine ⟨2502482372890638880399379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26693145310833481390926709 2502482372890638880399379)
                      ·
                        rfl

theorem cell23_4873567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_4873567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873567 prefixEnd_4873567 := by exact prefixLift 4873567
  have htrace : WordTrace (prefixWord ++ tailWord_4873567) baseStart_4873567 baseEnd_4873567 := by
    simpa [prefixWord, tailWord_4873567, baseEnd_4873567] using wordTrace_append hprefix tailTrace_4873567
  have hstable : (prefixWord ++ tailWord_4873567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873567).length < 2 ^ (prefixWord ++ tailWord_4873567).sum := by decide
  have hdescent : baseEnd_4873567 < baseStart_4873567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873594 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4]
def baseStart_4873594 : Nat := 118140960795 + 4873594 * 2 ^ 59
def prefixEnd_4873594 : Nat := 4983230072969 + 3 ^ 40 * 4873594 * 2
def baseEnd_4873594 : Nat := 2502496236868310274761755

theorem tailTrace_4873594 : CollatzResearch.WordTrace tailWord_4873594 prefixEnd_4873594 2502496236868310274761755 := by
  unfold tailWord_4873594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44438644076452189108512959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118503050870539170956034557 44438644076452189108512959)
  ·
    refine ⟨66657966114678283662769439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44438644076452189108512959 66657966114678283662769439)
    ·
      refine ⟨99986949172017425494154159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66657966114678283662769439 99986949172017425494154159)
      ·
        refine ⟨149980423758026138241231239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99986949172017425494154159 149980423758026138241231239)
        ·
          refine ⟨224970635637039207361846859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149980423758026138241231239 224970635637039207361846859)
          ·
            refine ⟨337455953455558811042770289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224970635637039207361846859 337455953455558811042770289)
            ·
              refine ⟨253091965091669108282077717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337455953455558811042770289 253091965091669108282077717)
              ·
                refine ⟨11863685863671989450722393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 253091965091669108282077717 11863685863671989450722393)
                ·
                  refine ⟨8897764397753992088041795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11863685863671989450722393 8897764397753992088041795)
                  ·
                    refine ⟨13346646596630988132062693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8897764397753992088041795 13346646596630988132062693)
                    ·
                      refine ⟨2502496236868310274761755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13346646596630988132062693 2502496236868310274761755)
                      ·
                        rfl

theorem cell23_4873594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_4873594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873594 prefixEnd_4873594 := by exact prefixLift 4873594
  have htrace : WordTrace (prefixWord ++ tailWord_4873594) baseStart_4873594 baseEnd_4873594 := by
    simpa [prefixWord, tailWord_4873594, baseEnd_4873594] using wordTrace_append hprefix tailTrace_4873594
  have hstable : (prefixWord ++ tailWord_4873594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873594).length < 2 ^ (prefixWord ++ tailWord_4873594).sum := by decide
  have hdescent : baseEnd_4873594 < baseStart_4873594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873601 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4873601 : Nat := 118140960795 + 4873601 * 2 ^ 59
def prefixEnd_4873601 : Nat := 4983230072969 + 3 ^ 40 * 4873601 * 2
def baseEnd_4873601 : Nat := 2502499831232891747374223

theorem tailTrace_4873601 : CollatzResearch.WordTrace tailWord_4873601 prefixEnd_4873601 2502499831232891747374223 := by
  unfold tailWord_4873601
  simp only [CollatzResearch.WordTrace]
  refine ⟨177754831616783396629556657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118503221077855597753037771 177754831616783396629556657)
  ·
    refine ⟨133316123712587547472167493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177754831616783396629556657 133316123712587547472167493)
    ·
      refine ⟨24996773196110165151031405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133316123712587547472167493 24996773196110165151031405)
      ·
        refine ⟨9373789948541311931636777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24996773196110165151031405 9373789948541311931636777)
        ·
          refine ⟨7030342461405983948727583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9373789948541311931636777 7030342461405983948727583)
          ·
            refine ⟨10545513692108975923091375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030342461405983948727583 10545513692108975923091375)
            ·
              refine ⟨15818270538163463884637063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10545513692108975923091375 15818270538163463884637063)
              ·
                refine ⟨23727405807245195826955595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15818270538163463884637063 23727405807245195826955595)
                ·
                  refine ⟨35591108710867793740433393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23727405807245195826955595 35591108710867793740433393)
                  ·
                    refine ⟨26693331533150845305325045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35591108710867793740433393 26693331533150845305325045)
                    ·
                      refine ⟨2502499831232891747374223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26693331533150845305325045 2502499831232891747374223)
                      ·
                        rfl

theorem cell23_4873601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4873601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873601 prefixEnd_4873601 := by exact prefixLift 4873601
  have htrace : WordTrace (prefixWord ++ tailWord_4873601) baseStart_4873601 baseEnd_4873601 := by
    simpa [prefixWord, tailWord_4873601, baseEnd_4873601] using wordTrace_append hprefix tailTrace_4873601
  have hstable : (prefixWord ++ tailWord_4873601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873601).length < 2 ^ (prefixWord ++ tailWord_4873601).sum := by decide
  have hdescent : baseEnd_4873601 < baseStart_4873601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873631 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3]
def baseStart_4873631 : Nat := 118140960795 + 4873631 * 2 ^ 59
def prefixEnd_4873631 : Nat := 4983230072969 + 3 ^ 40 * 4873631 * 2
def baseEnd_4873631 : Nat := 2502515235652526629999085

theorem tailTrace_4873631 : CollatzResearch.WordTrace tailWord_4873631 prefixEnd_4873631 2502515235652526629999085 := by
  unfold tailWord_4873631
  simp only [CollatzResearch.WordTrace]
  refine ⟨177755925806674711753148747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118503950537783141168765831 177755925806674711753148747)
  ·
    refine ⟨266633888710012067629723121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177755925806674711753148747 266633888710012067629723121)
    ·
      refine ⟨199975416532509050722292341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266633888710012067629723121 199975416532509050722292341)
      ·
        refine ⟨18747695299922723505214907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199975416532509050722292341 18747695299922723505214907)
        ·
          refine ⟨28121542949884085257822361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18747695299922723505214907 28121542949884085257822361)
          ·
            refine ⟨21091157212413063943366771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28121542949884085257822361 21091157212413063943366771)
            ·
              refine ⟨31636735818619595915050157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21091157212413063943366771 31636735818619595915050157)
              ·
                refine ⟨11863775931982348468143809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31636735818619595915050157 11863775931982348468143809)
                ·
                  refine ⟨8897831948986761351107857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11863775931982348468143809 8897831948986761351107857)
                  ·
                    refine ⟨6673373961740071013330893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8897831948986761351107857 6673373961740071013330893)
                    ·
                      refine ⟨2502515235652526629999085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673373961740071013330893 2502515235652526629999085)
                      ·
                        rfl

theorem cell23_4873631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_4873631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873631 prefixEnd_4873631 := by exact prefixLift 4873631
  have htrace : WordTrace (prefixWord ++ tailWord_4873631) baseStart_4873631 baseEnd_4873631 := by
    simpa [prefixWord, tailWord_4873631, baseEnd_4873631] using wordTrace_append hprefix tailTrace_4873631
  have hstable : (prefixWord ++ tailWord_4873631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873631).length < 2 ^ (prefixWord ++ tailWord_4873631).sum := by decide
  have hdescent : baseEnd_4873631 < baseStart_4873631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873664 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 3, 5]
def baseStart_4873664 : Nat := 118140960795 + 4873664 * 2 ^ 59
def prefixEnd_4873664 : Nat := 4983230072969 + 3 ^ 40 * 4873664 * 2
def baseEnd_4873664 : Nat := 834177393504708333628811

theorem tailTrace_4873664 : CollatzResearch.WordTrace tailWord_4873664 prefixEnd_4873664 834177393504708333628811 := by
  unfold tailWord_4873664
  simp only [CollatzResearch.WordTrace]
  refine ⟨88878564707777579194550023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118504752943703438926066697 88878564707777579194550023)
  ·
    refine ⟨133317847061666368791825035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88878564707777579194550023 133317847061666368791825035)
    ·
      refine ⟨199976770592499553187737553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133317847061666368791825035 199976770592499553187737553)
      ·
        refine ⟨149982577944374664890803165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199976770592499553187737553 149982577944374664890803165)
        ·
          refine ⟨56243466729140499334051187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149982577944374664890803165 56243466729140499334051187)
          ·
            refine ⟨84365200093710749001076781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56243466729140499334051187 84365200093710749001076781)
            ·
              refine ⟨31636950035141530875403793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84365200093710749001076781 31636950035141530875403793)
              ·
                refine ⟨23727712526356148156552845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31636950035141530875403793 23727712526356148156552845)
                ·
                  refine ⟨8897892197383555558707317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23727712526356148156552845 8897892197383555558707317)
                  ·
                    refine ⟨834177393504708333628811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8897892197383555558707317 834177393504708333628811)
                    ·
                      rfl

theorem cell23_4873664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 3, 5].length) (baseStart_4873664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873664 prefixEnd_4873664 := by exact prefixLift 4873664
  have htrace : WordTrace (prefixWord ++ tailWord_4873664) baseStart_4873664 baseEnd_4873664 := by
    simpa [prefixWord, tailWord_4873664, baseEnd_4873664] using wordTrace_append hprefix tailTrace_4873664
  have hstable : (prefixWord ++ tailWord_4873664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873664).length < 2 ^ (prefixWord ++ tailWord_4873664).sum := by decide
  have hdescent : baseEnd_4873664 < baseStart_4873664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873671 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_4873671 : Nat := 118140960795 + 4873671 * 2 ^ 59
def prefixEnd_4873671 : Nat := 4983230072969 + 3 ^ 40 * 4873671 * 2
def baseEnd_4873671 : Nat := 2502535774878706473498901

theorem tailTrace_4873671 : CollatzResearch.WordTrace tailWord_4873671 prefixEnd_4873671 2502535774878706473498901 := by
  unfold tailWord_4873671
  simp only [CollatzResearch.WordTrace]
  refine ⟨177757384726529798584604867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118504923151019865723069911 177757384726529798584604867)
  ·
    refine ⟨266636077089794697876907301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177757384726529798584604867 266636077089794697876907301)
    ·
      refine ⟨49994264454336505851920119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266636077089794697876907301 49994264454336505851920119)
      ·
        refine ⟨74991396681504758777880179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49994264454336505851920119 74991396681504758777880179)
        ·
          refine ⟨112487095022257138166820269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74991396681504758777880179 112487095022257138166820269)
          ·
            refine ⟨42182660633346426812557601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112487095022257138166820269 42182660633346426812557601)
            ·
              refine ⟨31636995475009820109418201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42182660633346426812557601 31636995475009820109418201)
              ·
                refine ⟨23727746606257365082063651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31636995475009820109418201 23727746606257365082063651)
                ·
                  refine ⟨35591619909386047623095477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23727746606257365082063651 35591619909386047623095477)
                  ·
                    refine ⟨3336714366504941964665201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35591619909386047623095477 3336714366504941964665201)
                    ·
                      refine ⟨2502535774878706473498901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336714366504941964665201 2502535774878706473498901)
                      ·
                        rfl

theorem cell23_4873671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_4873671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873671 prefixEnd_4873671 := by exact prefixLift 4873671
  have htrace : WordTrace (prefixWord ++ tailWord_4873671) baseStart_4873671 baseEnd_4873671 := by
    simpa [prefixWord, tailWord_4873671, baseEnd_4873671] using wordTrace_append hprefix tailTrace_4873671
  have hstable : (prefixWord ++ tailWord_4873671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873671).length < 2 ^ (prefixWord ++ tailWord_4873671).sum := by decide
  have hdescent : baseEnd_4873671 < baseStart_4873671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873688 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2]
def baseStart_4873688 : Nat := 118140960795 + 4873688 * 2 ^ 59
def prefixEnd_4873688 : Nat := 4983230072969 + 3 ^ 40 * 4873688 * 2
def baseEnd_4873688 : Nat := 2502544504049832906986323

theorem tailTrace_4873688 : CollatzResearch.WordTrace tailWord_4873688 prefixEnd_4873688 2502544504049832906986323 := by
  unfold tailWord_4873688
  simp only [CollatzResearch.WordTrace]
  refine ⟨88879002383734105243986859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118505336511645473658649145 88879002383734105243986859)
  ·
    refine ⟨133318503575601157865980289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88879002383734105243986859 133318503575601157865980289)
    ·
      refine ⟨99988877681700868399485217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133318503575601157865980289 99988877681700868399485217)
      ·
        refine ⟨74991658261275651299613913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99988877681700868399485217 74991658261275651299613913)
        ·
          refine ⟨56243743695956738474710435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74991658261275651299613913 56243743695956738474710435)
          ·
            refine ⟨84365615543935107712065653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56243743695956738474710435 84365615543935107712065653)
            ·
              refine ⟨7909276457243916348006155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84365615543935107712065653 7909276457243916348006155)
              ·
                refine ⟨11863914685865874522009233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7909276457243916348006155 11863914685865874522009233)
                ·
                  refine ⟨8897936014399405891506925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11863914685865874522009233 8897936014399405891506925)
                  ·
                    refine ⟨3336726005399777209315097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8897936014399405891506925 3336726005399777209315097)
                    ·
                      refine ⟨2502544504049832906986323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336726005399777209315097 2502544504049832906986323)
                      ·
                        rfl

theorem cell23_4873688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 2, 3, 2].length) (baseStart_4873688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873688 prefixEnd_4873688 := by exact prefixLift 4873688
  have htrace : WordTrace (prefixWord ++ tailWord_4873688) baseStart_4873688 baseEnd_4873688 := by
    simpa [prefixWord, tailWord_4873688, baseEnd_4873688] using wordTrace_append hprefix tailTrace_4873688
  have hstable : (prefixWord ++ tailWord_4873688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873688).length < 2 ^ (prefixWord ++ tailWord_4873688).sum := by decide
  have hdescent : baseEnd_4873688 < baseStart_4873688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873695 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 1, 1, 3]
def baseStart_4873695 : Nat := 118140960795 + 4873695 * 2 ^ 59
def prefixEnd_4873695 : Nat := 4983230072969 + 3 ^ 40 * 4873695 * 2
def baseEnd_4873695 : Nat := 2502548098414414379598791

theorem tailTrace_4873695 : CollatzResearch.WordTrace tailWord_4873695 prefixEnd_4873695 2502548098414414379598791 := by
  unfold tailWord_4873695
  simp only [CollatzResearch.WordTrace]
  refine ⟨177758260078442850683478539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118505506718961900455652359 177758260078442850683478539)
  ·
    refine ⟨266637390117664276025217809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177758260078442850683478539 266637390117664276025217809)
    ·
      refine ⟨199978042588248207018913357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266637390117664276025217809 199978042588248207018913357)
      ·
        refine ⟨74991765970593077632092509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 199978042588248207018913357 74991765970593077632092509)
        ·
          refine ⟨28121912238972404112034691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74991765970593077632092509 28121912238972404112034691)
          ·
            refine ⟨42182868358458606168052037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28121912238972404112034691 42182868358458606168052037)
            ·
              refine ⟨7909287817210988656509757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42182868358458606168052037 7909287817210988656509757)
              ·
                refine ⟨2965982931454120746191159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7909287817210988656509757 2965982931454120746191159)
                ·
                  refine ⟨4448974397181181119286739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2965982931454120746191159 4448974397181181119286739)
                  ·
                    refine ⟨6673461595771771678930109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4448974397181181119286739 6673461595771771678930109)
                    ·
                      refine ⟨2502548098414414379598791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673461595771771678930109 2502548098414414379598791)
                      ·
                        rfl

theorem cell23_4873695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 1, 3].length) (baseStart_4873695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873695 prefixEnd_4873695 := by exact prefixLift 4873695
  have htrace : WordTrace (prefixWord ++ tailWord_4873695) baseStart_4873695 baseEnd_4873695 := by
    simpa [prefixWord, tailWord_4873695, baseEnd_4873695] using wordTrace_append hprefix tailTrace_4873695
  have hstable : (prefixWord ++ tailWord_4873695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873695).length < 2 ^ (prefixWord ++ tailWord_4873695).sum := by decide
  have hdescent : baseEnd_4873695 < baseStart_4873695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873735 : List Nat := [1, 1, 4, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_4873735 : Nat := 118140960795 + 4873735 * 2 ^ 59
def prefixEnd_4873735 : Nat := 4983230072969 + 3 ^ 40 * 4873735 * 2
def baseEnd_4873735 : Nat := 2502568637640594223098607

theorem tailTrace_4873735 : CollatzResearch.WordTrace tailWord_4873735 prefixEnd_4873735 2502568637640594223098607 := by
  unfold tailWord_4873735
  simp only [CollatzResearch.WordTrace]
  refine ⟨177759718998297937514934659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118506479332198625009956439 177759718998297937514934659)
  ·
    refine ⟨266639578497446906272401989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177759718998297937514934659 266639578497446906272401989)
    ·
      refine ⟨49994920968271294926075373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266639578497446906272401989 49994920968271294926075373)
      ·
        refine ⟨18748095363101735597278265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49994920968271294926075373 18748095363101735597278265)
        ·
          refine ⟨14061071522326301697958699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18748095363101735597278265 14061071522326301697958699)
          ·
            refine ⟨21091607283489452546938049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14061071522326301697958699 21091607283489452546938049)
            ·
              refine ⟨15818705462617089410203537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21091607283489452546938049 15818705462617089410203537)
              ·
                refine ⟨11864029096962817057652653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15818705462617089410203537 11864029096962817057652653)
                ·
                  refine ⟨4449010911361056396619745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11864029096962817057652653 4449010911361056396619745)
                  ·
                    refine ⟨3336758183520792297464809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449010911361056396619745 3336758183520792297464809)
                    ·
                      refine ⟨2502568637640594223098607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336758183520792297464809 2502568637640594223098607)
                      ·
                        rfl

theorem cell23_4873735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_4873735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873735 prefixEnd_4873735 := by exact prefixLift 4873735
  have htrace : WordTrace (prefixWord ++ tailWord_4873735) baseStart_4873735 baseEnd_4873735 := by
    simpa [prefixWord, tailWord_4873735, baseEnd_4873735] using wordTrace_append hprefix tailTrace_4873735
  have hstable : (prefixWord ++ tailWord_4873735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873735).length < 2 ^ (prefixWord ++ tailWord_4873735).sum := by decide
  have hdescent : baseEnd_4873735 < baseStart_4873735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873738 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3]
def baseStart_4873738 : Nat := 118140960795 + 4873738 * 2 ^ 59
def prefixEnd_4873738 : Nat := 4983230072969 + 3 ^ 40 * 4873738 * 2
def baseEnd_4873738 : Nat := 2502570178082557711361093

theorem tailTrace_4873738 : CollatzResearch.WordTrace tailWord_4873738 prefixEnd_4873738 2502570178082557711361093 := by
  unfold tailWord_4873738
  simp only [CollatzResearch.WordTrace]
  refine ⟨44439957104321767256823467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118506552278191379351529245 44439957104321767256823467)
  ·
    refine ⟨66659935656482650885235201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44439957104321767256823467 66659935656482650885235201)
    ·
      refine ⟨49994951742361988163926401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66659935656482650885235201 49994951742361988163926401)
      ·
        refine ⟨37496213806771491122944801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49994951742361988163926401 37496213806771491122944801)
        ·
          refine ⟨28122160355078618342208601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37496213806771491122944801 28122160355078618342208601)
          ·
            refine ⟨21091620266308963756656451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28122160355078618342208601 21091620266308963756656451)
            ·
              refine ⟨31637430399463445634984677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21091620266308963756656451 31637430399463445634984677)
              ·
                refine ⟨5932018199899396056559627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31637430399463445634984677 5932018199899396056559627)
                ·
                  refine ⟨8898027299849094084839441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5932018199899396056559627 8898027299849094084839441)
                  ·
                    refine ⟨6673520474886820563629581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8898027299849094084839441 6673520474886820563629581)
                    ·
                      refine ⟨2502570178082557711361093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673520474886820563629581 2502570178082557711361093)
                      ·
                        rfl

theorem cell23_4873738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_4873738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873738 prefixEnd_4873738 := by exact prefixLift 4873738
  have htrace : WordTrace (prefixWord ++ tailWord_4873738) baseStart_4873738 baseEnd_4873738 := by
    simpa [prefixWord, tailWord_4873738, baseEnd_4873738] using wordTrace_append hprefix tailTrace_4873738
  have hstable : (prefixWord ++ tailWord_4873738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873738).length < 2 ^ (prefixWord ++ tailWord_4873738).sum := by decide
  have hdescent : baseEnd_4873738 < baseStart_4873738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873754 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_4873754 : Nat := 118140960795 + 4873754 * 2 ^ 59
def prefixEnd_4873754 : Nat := 4983230072969 + 3 ^ 40 * 4873754 * 2
def baseEnd_4873754 : Nat := 834192797924343216253673

theorem tailTrace_4873754 : CollatzResearch.WordTrace tailWord_4873754 prefixEnd_4873754 834192797924343216253673 := by
  unfold tailWord_4873754
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440102996307275939969079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118506941323486069173250877 44440102996307275939969079)
  ·
    refine ⟨66660154494460913909953619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44440102996307275939969079 66660154494460913909953619)
    ·
      refine ⟨99990231741691370864930429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66660154494460913909953619 99990231741691370864930429)
      ·
        refine ⟨37496336903134264074348911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99990231741691370864930429 37496336903134264074348911)
        ·
          refine ⟨56244505354701396111523367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37496336903134264074348911 56244505354701396111523367)
          ·
            refine ⟨84366758032052094167285051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56244505354701396111523367 84366758032052094167285051)
            ·
              refine ⟨126550137048078141250927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84366758032052094167285051 126550137048078141250927577)
              ·
                refine ⟨94912602786058605938195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126550137048078141250927577 94912602786058605938195683)
                ·
                  refine ⟨142368904179087908907293525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94912602786058605938195683 142368904179087908907293525)
                  ·
                    refine ⟨834192797924343216253673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 142368904179087908907293525 834192797924343216253673)
                    ·
                      rfl

theorem cell23_4873754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_4873754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873754 prefixEnd_4873754 := by exact prefixLift 4873754
  have htrace : WordTrace (prefixWord ++ tailWord_4873754) baseStart_4873754 baseEnd_4873754 := by
    simpa [prefixWord, tailWord_4873754, baseEnd_4873754] using wordTrace_append hprefix tailTrace_4873754
  have hstable : (prefixWord ++ tailWord_4873754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873754).length < 2 ^ (prefixWord ++ tailWord_4873754).sum := by decide
  have hdescent : baseEnd_4873754 < baseStart_4873754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873778 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2]
def baseStart_4873778 : Nat := 118140960795 + 4873778 * 2 ^ 59
def prefixEnd_4873778 : Nat := 4983230072969 + 3 ^ 40 * 4873778 * 2
def baseEnd_4873778 : Nat := 2502590717308737554860909

theorem tailTrace_4873778 : CollatzResearch.WordTrace tailWord_4873778 prefixEnd_4873778 2502590717308737554860909 := by
  unfold tailWord_4873778
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440321834285538964687497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118507524891428103905833325 44440321834285538964687497)
  ·
    refine ⟨33330241375714154223515623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44440321834285538964687497 33330241375714154223515623)
    ·
      refine ⟨49995362063571231335273435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33330241375714154223515623 49995362063571231335273435)
      ·
        refine ⟨74993043095356847002910153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49995362063571231335273435 74993043095356847002910153)
        ·
          refine ⟨56244782321517635252182615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74993043095356847002910153 56244782321517635252182615)
          ·
            refine ⟨84367173482276452878273923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56244782321517635252182615 84367173482276452878273923)
            ·
              refine ⟨126550760223414679317410885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84367173482276452878273923 126550760223414679317410885)
              ·
                refine ⟨23728267541890252372014541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126550760223414679317410885 23728267541890252372014541)
                ·
                  refine ⟨8898100328208844639505453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23728267541890252372014541 8898100328208844639505453)
                  ·
                    refine ⟨3336787623078316739814545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8898100328208844639505453 3336787623078316739814545)
                    ·
                      refine ⟨2502590717308737554860909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336787623078316739814545 2502590717308737554860909)
                      ·
                        rfl

theorem cell23_4873778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_4873778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873778 prefixEnd_4873778 := by exact prefixLift 4873778
  have htrace : WordTrace (prefixWord ++ tailWord_4873778) baseStart_4873778 baseEnd_4873778 := by
    simpa [prefixWord, tailWord_4873778, baseEnd_4873778] using wordTrace_append hprefix tailTrace_4873778
  have hstable : (prefixWord ++ tailWord_4873778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873778).length < 2 ^ (prefixWord ++ tailWord_4873778).sum := by decide
  have hdescent : baseEnd_4873778 < baseStart_4873778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873785 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4873785 : Nat := 118140960795 + 4873785 * 2 ^ 59
def prefixEnd_4873785 : Nat := 4983230072969 + 3 ^ 40 * 4873785 * 2
def baseEnd_4873785 : Nat := 2502594311673319027473377

theorem tailTrace_4873785 : CollatzResearch.WordTrace tailWord_4873785 prefixEnd_4873785 2502594311673319027473377 := by
  unfold tailWord_4873785
  simp only [CollatzResearch.WordTrace]
  refine ⟨177761542648116796054254809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118507695098744530702836539 177761542648116796054254809)
  ·
    refine ⟨133321156986087597040691107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177761542648116796054254809 133321156986087597040691107)
    ·
      refine ⟨199981735479131395561036661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133321156986087597040691107 199981735479131395561036661)
      ·
        refine ⟨18748287701168568333847187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 199981735479131395561036661 18748287701168568333847187)
        ·
          refine ⟨28122431551752852500770781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18748287701168568333847187 28122431551752852500770781)
          ·
            refine ⟨10545911831907319687789043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28122431551752852500770781 10545911831907319687789043)
            ·
              refine ⟨15818867747860979531683565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10545911831907319687789043 15818867747860979531683565)
              ·
                refine ⟨5932075405447867324381337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15818867747860979531683565 5932075405447867324381337)
                ·
                  refine ⟨4449056554085900493286003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932075405447867324381337 4449056554085900493286003)
                  ·
                    refine ⟨6673584831128850739929005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4449056554085900493286003 6673584831128850739929005)
                    ·
                      refine ⟨2502594311673319027473377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673584831128850739929005 2502594311673319027473377)
                      ·
                        rfl

theorem cell23_4873785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4873785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873785 prefixEnd_4873785 := by exact prefixLift 4873785
  have htrace : WordTrace (prefixWord ++ tailWord_4873785) baseStart_4873785 baseEnd_4873785 := by
    simpa [prefixWord, tailWord_4873785, baseEnd_4873785] using wordTrace_append hprefix tailTrace_4873785
  have hstable : (prefixWord ++ tailWord_4873785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873785).length < 2 ^ (prefixWord ++ tailWord_4873785).sum := by decide
  have hdescent : baseEnd_4873785 < baseStart_4873785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873808 : List Nat := [2, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2]
def baseStart_4873808 : Nat := 118140960795 + 4873808 * 2 ^ 59
def prefixEnd_4873808 : Nat := 4983230072969 + 3 ^ 40 * 4873808 * 2
def baseEnd_4873808 : Nat := 2502606121728372437485771

theorem tailTrace_4873808 : CollatzResearch.WordTrace tailWord_4873808 prefixEnd_4873808 2502606121728372437485771 := by
  unfold tailWord_4873808
  simp only [CollatzResearch.WordTrace]
  refine ⟨88881190763516735491171039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118508254351355647321561385 88881190763516735491171039)
  ·
    refine ⟨133321786145275103236756559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88881190763516735491171039 133321786145275103236756559)
    ·
      refine ⟨199982679217912654855134839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133321786145275103236756559 199982679217912654855134839)
      ·
        refine ⟨299974018826868982282702259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199982679217912654855134839 299974018826868982282702259)
        ·
          refine ⟨449961028240303473424053389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299974018826868982282702259 449961028240303473424053389)
          ·
            refine ⟨168735385590113802534020021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 449961028240303473424053389 168735385590113802534020021)
            ·
              refine ⟨15818942399073168987564377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168735385590113802534020021 15818942399073168987564377)
              ·
                refine ⟨11864206799304876740673283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15818942399073168987564377 11864206799304876740673283)
                ·
                  refine ⟨17796310198957315111009925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11864206799304876740673283 17796310198957315111009925)
                  ·
                    refine ⟨3336808162304496583314361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17796310198957315111009925 3336808162304496583314361)
                    ·
                      refine ⟨2502606121728372437485771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336808162304496583314361 2502606121728372437485771)
                      ·
                        rfl

theorem cell23_4873808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 2, 1, 4, 2].length) (baseStart_4873808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873808 prefixEnd_4873808 := by exact prefixLift 4873808
  have htrace : WordTrace (prefixWord ++ tailWord_4873808) baseStart_4873808 baseEnd_4873808 := by
    simpa [prefixWord, tailWord_4873808, baseEnd_4873808] using wordTrace_append hprefix tailTrace_4873808
  have hstable : (prefixWord ++ tailWord_4873808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873808).length < 2 ^ (prefixWord ++ tailWord_4873808).sum := by decide
  have hdescent : baseEnd_4873808 < baseStart_4873808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873812 : List Nat := [2, 4, 1, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_4873812 : Nat := 118140960795 + 4873812 * 2 ^ 59
def prefixEnd_4873812 : Nat := 4983230072969 + 3 ^ 40 * 4873812 * 2
def baseEnd_4873812 : Nat := 2502608175650990421835753

theorem tailTrace_4873812 : CollatzResearch.WordTrace tailWord_4873812 prefixEnd_4873812 2502608175650990421835753 := by
  unfold tailWord_4873812
  simp only [CollatzResearch.WordTrace]
  refine ⟨88881263709509489832743845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118508351612679319776991793 88881263709509489832743845)
  ·
    refine ⟨16665236945533029343639471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88881263709509489832743845 16665236945533029343639471)
    ·
      refine ⟨24997855418299544015459207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16665236945533029343639471 24997855418299544015459207)
      ·
        refine ⟨37496783127449316023188811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24997855418299544015459207 37496783127449316023188811)
        ·
          refine ⟨56245174691173974034783217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37496783127449316023188811 56245174691173974034783217)
          ·
            refine ⟨42183881018380480526087413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56245174691173974034783217 42183881018380480526087413)
            ·
              refine ⟨3954738845473170049320695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42183881018380480526087413 3954738845473170049320695)
              ·
                refine ⟨5932108268209755073981043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3954738845473170049320695 5932108268209755073981043)
                ·
                  refine ⟨8898162402314632610971565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5932108268209755073981043 8898162402314632610971565)
                  ·
                    refine ⟨3336810900867987229114337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8898162402314632610971565 3336810900867987229114337)
                    ·
                      refine ⟨2502608175650990421835753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336810900867987229114337 2502608175650990421835753)
                      ·
                        rfl

theorem cell23_4873812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_4873812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873812 prefixEnd_4873812 := by exact prefixLift 4873812
  have htrace : WordTrace (prefixWord ++ tailWord_4873812) baseStart_4873812 baseEnd_4873812 := by
    simpa [prefixWord, tailWord_4873812, baseEnd_4873812] using wordTrace_append hprefix tailTrace_4873812
  have hstable : (prefixWord ++ tailWord_4873812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873812).length < 2 ^ (prefixWord ++ tailWord_4873812).sum := by decide
  have hdescent : baseEnd_4873812 < baseStart_4873812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873842 : List Nat := [3, 2, 1, 2, 3, 1, 2, 3, 2, 2, 2]
def baseStart_4873842 : Nat := 118140960795 + 4873842 * 2 ^ 59
def prefixEnd_4873842 : Nat := 4983230072969 + 3 ^ 40 * 4873842 * 2
def baseEnd_4873842 : Nat := 2502623580070625304460615

theorem tailTrace_4873842 : CollatzResearch.WordTrace tailWord_4873842 prefixEnd_4873842 2502623580070625304460615 := by
  unfold tailWord_4873842
  simp only [CollatzResearch.WordTrace]
  refine ⟨44440905402227573697269945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118509081072606863192719853 44440905402227573697269945)
  ·
    refine ⟨33330679051670680272952459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44440905402227573697269945 33330679051670680272952459)
    ·
      refine ⟨49996018577506020409428689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33330679051670680272952459 49996018577506020409428689)
      ·
        refine ⟨37497013933129515307071517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49996018577506020409428689 37497013933129515307071517)
        ·
          refine ⟨14061380224923568240151819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37497013933129515307071517 14061380224923568240151819)
          ·
            refine ⟨21092070337385352360227729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14061380224923568240151819 21092070337385352360227729)
            ·
              refine ⟨15819052753039014270170797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21092070337385352360227729 15819052753039014270170797)
              ·
                refine ⟨5932144782389630351314049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15819052753039014270170797 5932144782389630351314049)
                ·
                  refine ⟨4449108586792222763485537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932144782389630351314049 4449108586792222763485537)
                  ·
                    refine ⟨3336831440094167072614153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449108586792222763485537 3336831440094167072614153)
                    ·
                      refine ⟨2502623580070625304460615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336831440094167072614153 2502623580070625304460615)
                      ·
                        rfl

theorem cell23_4873842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_4873842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873842 prefixEnd_4873842 := by exact prefixLift 4873842
  have htrace : WordTrace (prefixWord ++ tailWord_4873842) baseStart_4873842 baseEnd_4873842 := by
    simpa [prefixWord, tailWord_4873842, baseEnd_4873842] using wordTrace_append hprefix tailTrace_4873842
  have hstable : (prefixWord ++ tailWord_4873842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873842).length < 2 ^ (prefixWord ++ tailWord_4873842).sum := by decide
  have hdescent : baseEnd_4873842 < baseStart_4873842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873861 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_4873861 : Nat := 118140960795 + 4873861 * 2 ^ 59
def prefixEnd_4873861 : Nat := 4983230072969 + 3 ^ 40 * 4873861 * 2
def baseEnd_4873861 : Nat := 834211112067686910041009

theorem tailTrace_4873861 : CollatzResearch.WordTrace tailWord_4873861 prefixEnd_4873861 834211112067686910041009 := by
  unfold tailWord_4873861
  simp only [CollatzResearch.WordTrace]
  refine ⟨177764314595841461034021437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118509543063894307356014291 177764314595841461034021437)
  ·
    refine ⟨66661617973440547887758039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177764314595841461034021437 66661617973440547887758039)
    ·
      refine ⟨99992426960160821831637059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66661617973440547887758039 99992426960160821831637059)
      ·
        refine ⟨149988640440241232747455589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99992426960160821831637059 149988640440241232747455589)
        ·
          refine ⟨28122870082545231140147923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 149988640440241232747455589 28122870082545231140147923)
          ·
            refine ⟨42184305123817846710221885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28122870082545231140147923 42184305123817846710221885)
            ·
              refine ⟨15819114421431692516333207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42184305123817846710221885 15819114421431692516333207)
              ·
                refine ⟨23728671632147538774499811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15819114421431692516333207 23728671632147538774499811)
                ·
                  refine ⟨35593007448221308161749717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23728671632147538774499811 35593007448221308161749717)
                  ·
                    refine ⟨834211112067686910041009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35593007448221308161749717 834211112067686910041009)
                    ·
                      rfl

theorem cell23_4873861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_4873861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873861 prefixEnd_4873861 := by exact prefixLift 4873861
  have htrace : WordTrace (prefixWord ++ tailWord_4873861) baseStart_4873861 baseEnd_4873861 := by
    simpa [prefixWord, tailWord_4873861, baseEnd_4873861] using wordTrace_append hprefix tailTrace_4873861
  have hstable : (prefixWord ++ tailWord_4873861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873861).length < 2 ^ (prefixWord ++ tailWord_4873861).sum := by decide
  have hdescent : baseEnd_4873861 < baseStart_4873861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873876 : List Nat := [2, 4, 2, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_4873876 : Nat := 118140960795 + 4873876 * 2 ^ 59
def prefixEnd_4873876 : Nat := 4983230072969 + 3 ^ 40 * 4873876 * 2
def baseEnd_4873876 : Nat := 2502641038412878171435459

theorem tailTrace_4873876 : CollatzResearch.WordTrace tailWord_4873876 prefixEnd_4873876 2502641038412878171435459 := by
  unfold tailWord_4873876
  simp only [CollatzResearch.WordTrace]
  refine ⟨88882430845393559297908741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118509907793858079063878321 88882430845393559297908741)
  ·
    refine ⟨16665455783511292368357889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88882430845393559297908741 16665455783511292368357889)
    ·
      refine ⟨12499091837633469276268417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16665455783511292368357889 12499091837633469276268417)
      ·
        refine ⟨9374318878225101957201313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12499091837633469276268417 9374318878225101957201313)
        ·
          refine ⟨7030739158668826467900985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9374318878225101957201313 7030739158668826467900985)
          ·
            refine ⟨5273054369001619850925739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7030739158668826467900985 5273054369001619850925739)
            ·
              refine ⟨7909581553502429776388609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273054369001619850925739 7909581553502429776388609)
              ·
                refine ⟨5932186165126822332291457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7909581553502429776388609 5932186165126822332291457)
                ·
                  refine ⟨4449139623845116749218593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932186165126822332291457 4449139623845116749218593)
                  ·
                    refine ⟨3336854717883837561913945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449139623845116749218593 3336854717883837561913945)
                    ·
                      refine ⟨2502641038412878171435459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336854717883837561913945 2502641038412878171435459)
                      ·
                        rfl

theorem cell23_4873876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_4873876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873876 prefixEnd_4873876 := by exact prefixLift 4873876
  have htrace : WordTrace (prefixWord ++ tailWord_4873876) baseStart_4873876 baseEnd_4873876 := by
    simpa [prefixWord, tailWord_4873876, baseEnd_4873876] using wordTrace_append hprefix tailTrace_4873876
  have hstable : (prefixWord ++ tailWord_4873876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873876).length < 2 ^ (prefixWord ++ tailWord_4873876).sum := by decide
  have hdescent : baseEnd_4873876 < baseStart_4873876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873938 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 8]
def baseStart_4873938 : Nat := 118140960795 + 4873938 * 2 ^ 59
def prefixEnd_4873938 : Nat := 4983230072969 + 3 ^ 40 * 4873938 * 2
def baseEnd_4873938 : Nat := 278074763801495214317797

theorem tailTrace_4873938 : CollatzResearch.WordTrace tailWord_4873938 prefixEnd_4873938 278074763801495214317797 := by
  unfold tailWord_4873938
  simp only [CollatzResearch.WordTrace]
  refine ⟨44441780754140625796143617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118511415344375002123049645 44441780754140625796143617)
  ·
    refine ⟨33331335565605469347107713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44441780754140625796143617 33331335565605469347107713)
    ·
      refine ⟨24998501674204102010330785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33331335565605469347107713 24998501674204102010330785)
      ·
        refine ⟨18748876255653076507748089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24998501674204102010330785 18748876255653076507748089)
        ·
          refine ⟨14061657191739807380811067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18748876255653076507748089 14061657191739807380811067)
          ·
            refine ⟨21092485787609711071216601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14061657191739807380811067 21092485787609711071216601)
            ·
              refine ⟨15819364340707283303412451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21092485787609711071216601 15819364340707283303412451)
              ·
                refine ⟨23729046511060924955118677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15819364340707283303412451 23729046511060924955118677)
                ·
                  refine ⟨278074763801495214317797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23729046511060924955118677 278074763801495214317797)
                  ·
                    rfl

theorem cell23_4873938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_4873938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873938 prefixEnd_4873938 := by exact prefixLift 4873938
  have htrace : WordTrace (prefixWord ++ tailWord_4873938) baseStart_4873938 baseEnd_4873938 := by
    simpa [prefixWord, tailWord_4873938, baseEnd_4873938] using wordTrace_append hprefix tailTrace_4873938
  have hstable : (prefixWord ++ tailWord_4873938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873938).length < 2 ^ (prefixWord ++ tailWord_4873938).sum := by decide
  have hdescent : baseEnd_4873938 < baseStart_4873938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873955 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 6]
def baseStart_4873955 : Nat := 118140960795 + 4873955 * 2 ^ 59
def prefixEnd_4873955 : Nat := 4983230072969 + 3 ^ 40 * 4873955 * 2
def baseEnd_4873955 : Nat := 278075733709398151371955

theorem tailTrace_4873955 : CollatzResearch.WordTrace tailWord_4873955 prefixEnd_4873955 278075733709398151371955 := by
  unfold tailWord_4873955
  simp only [CollatzResearch.WordTrace]
  refine ⟨177767743057500915087943319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118511828705000610058628879 177767743057500915087943319)
  ·
    refine ⟨266651614586251372631914979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177767743057500915087943319 266651614586251372631914979)
    ·
      refine ⟨399977421879377058947872469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266651614586251372631914979 399977421879377058947872469)
      ·
        refine ⟨9374470825297899819090761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 399977421879377058947872469 9374470825297899819090761)
        ·
          refine ⟨7030853118973424864318071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9374470825297899819090761 7030853118973424864318071)
          ·
            refine ⟨10546279678460137296477107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7030853118973424864318071 10546279678460137296477107)
            ·
              refine ⟨15819419517690205944715661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10546279678460137296477107 15819419517690205944715661)
              ·
                refine ⟨5932282319133827229268373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15819419517690205944715661 5932282319133827229268373)
                ·
                  refine ⟨278075733709398151371955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5932282319133827229268373 278075733709398151371955)
                  ·
                    rfl

theorem cell23_4873955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 6].length) (baseStart_4873955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873955 prefixEnd_4873955 := by exact prefixLift 4873955
  have htrace : WordTrace (prefixWord ++ tailWord_4873955) baseStart_4873955 baseEnd_4873955 := by
    simpa [prefixWord, tailWord_4873955, baseEnd_4873955] using wordTrace_append hprefix tailTrace_4873955
  have hstable : (prefixWord ++ tailWord_4873955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873955).length < 2 ^ (prefixWord ++ tailWord_4873955).sum := by decide
  have hdescent : baseEnd_4873955 < baseStart_4873955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873968 : List Nat := [2, 1, 1, 1, 3, 1, 2, 6, 1, 5]
def baseStart_4873968 : Nat := 118140960795 + 4873968 * 2 ^ 59
def prefixEnd_4873968 : Nat := 4983230072969 + 3 ^ 40 * 4873968 * 2
def baseEnd_4873968 : Nat := 834229426211030603828345

theorem tailTrace_4873968 : CollatzResearch.WordTrace tailWord_4873968 prefixEnd_4873968 834229426211030603828345 := by
  unfold tailWord_4873968
  simp only [CollatzResearch.WordTrace]
  refine ⟨88884108603226909154083279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118512144804302545538777705 88884108603226909154083279)
  ·
    refine ⟨133326162904840363731124919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88884108603226909154083279 133326162904840363731124919)
    ·
      refine ⟨199989244357260545596687379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133326162904840363731124919 199989244357260545596687379)
      ·
        refine ⟨299983866535890818395031069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199989244357260545596687379 299983866535890818395031069)
        ·
          refine ⟨112493949950959056898136651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299983866535890818395031069 112493949950959056898136651)
          ·
            refine ⟨168740924926438585347204977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112493949950959056898136651 168740924926438585347204977)
            ·
              refine ⟨126555693694828939010403733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168740924926438585347204977 126555693694828939010403733)
              ·
                refine ⟨5932298141945106516112675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126555693694828939010403733 5932298141945106516112675)
                ·
                  refine ⟨8898447212917659774169013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5932298141945106516112675 8898447212917659774169013)
                  ·
                    refine ⟨834229426211030603828345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8898447212917659774169013 834229426211030603828345)
                    ·
                      rfl

theorem cell23_4873968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 6, 1, 5].length) (baseStart_4873968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873968 prefixEnd_4873968 := by exact prefixLift 4873968
  have htrace : WordTrace (prefixWord ++ tailWord_4873968) baseStart_4873968 baseEnd_4873968 := by
    simpa [prefixWord, tailWord_4873968, baseEnd_4873968] using wordTrace_append hprefix tailTrace_4873968
  have hstable : (prefixWord ++ tailWord_4873968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873968).length < 2 ^ (prefixWord ++ tailWord_4873968).sum := by decide
  have hdescent : baseEnd_4873968 < baseStart_4873968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4873975 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 2, 3, 2]
def baseStart_4873975 : Nat := 118140960795 + 4873975 * 2 ^ 59
def prefixEnd_4873975 : Nat := 4983230072969 + 3 ^ 40 * 4873975 * 2
def baseEnd_4873975 : Nat := 2502691872997673284097503

theorem tailTrace_4873975 : CollatzResearch.WordTrace tailWord_4873975 prefixEnd_4873975 2502691872997673284097503 := by
  unfold tailWord_4873975
  simp only [CollatzResearch.WordTrace]
  refine ⟨177768472517428458503671379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118512315011618972335780919 177768472517428458503671379)
  ·
    refine ⟨266652708776142687755507069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177768472517428458503671379 266652708776142687755507069)
    ·
      refine ⟨99994765791053507908315151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266652708776142687755507069 99994765791053507908315151)
      ·
        refine ⟨149992148686580261862472727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99994765791053507908315151 149992148686580261862472727)
        ·
          refine ⟨224988223029870392793709091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149992148686580261862472727 224988223029870392793709091)
          ·
            refine ⟨337482334544805589190563637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224988223029870392793709091 337482334544805589190563637)
            ·
              refine ⟨31638968863575523986615341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337482334544805589190563637 31638968863575523986615341)
              ·
                refine ⟨11864613323840821494980753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31638968863575523986615341 11864613323840821494980753)
                ·
                  refine ⟨8898459992880616121235565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11864613323840821494980753 8898459992880616121235565)
                  ·
                    refine ⟨3336922497330231045463337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8898459992880616121235565 3336922497330231045463337)
                    ·
                      refine ⟨2502691872997673284097503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3336922497330231045463337 2502691872997673284097503)
                      ·
                        rfl

theorem cell23_4873975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 3, 2].length) (baseStart_4873975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4873975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4873975 prefixEnd_4873975 := by exact prefixLift 4873975
  have htrace : WordTrace (prefixWord ++ tailWord_4873975) baseStart_4873975 baseEnd_4873975 := by
    simpa [prefixWord, tailWord_4873975, baseEnd_4873975] using wordTrace_append hprefix tailTrace_4873975
  have hstable : (prefixWord ++ tailWord_4873975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4873975).length < 2 ^ (prefixWord ++ tailWord_4873975).sum := by decide
  have hdescent : baseEnd_4873975 < baseStart_4873975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4873975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874008 : List Nat := [2, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5]
def baseStart_4874008 : Nat := 118140960795 + 4874008 * 2 ^ 59
def prefixEnd_4874008 : Nat := 4983230072969 + 3 ^ 40 * 4874008 * 2
def baseEnd_4874008 : Nat := 2502708817859271654984851

theorem tailTrace_4874008 : CollatzResearch.WordTrace tailWord_4874008 prefixEnd_4874008 2502708817859271654984851 := by
  unfold tailWord_4874008
  simp only [CollatzResearch.WordTrace]
  refine ⟨88884838063154452569811339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118513117417539270093081785 88884838063154452569811339)
  ·
    refine ⟨133327257094731678854717009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88884838063154452569811339 133327257094731678854717009)
    ·
      refine ⟨99995442821048759141037757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133327257094731678854717009 99995442821048759141037757)
      ·
        refine ⟨37498291057893284677889159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99995442821048759141037757 37498291057893284677889159)
        ·
          refine ⟨56247436586839927016833739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37498291057893284677889159 56247436586839927016833739)
          ·
            refine ⟨84371154880259890525250609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56247436586839927016833739 84371154880259890525250609)
            ·
              refine ⟨63278366160194917893937957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84371154880259890525250609 63278366160194917893937957)
              ·
                refine ⟨11864693655036547105113367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63278366160194917893937957 11864693655036547105113367)
                ·
                  refine ⟨17797040482554820657670051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11864693655036547105113367 17797040482554820657670051)
                  ·
                    refine ⟨26695560723832230986505077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17797040482554820657670051 26695560723832230986505077)
                    ·
                      refine ⟨2502708817859271654984851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26695560723832230986505077 2502708817859271654984851)
                      ·
                        rfl

theorem cell23_4874008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_4874008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874008 prefixEnd_4874008 := by exact prefixLift 4874008
  have htrace : WordTrace (prefixWord ++ tailWord_4874008) baseStart_4874008 baseEnd_4874008 := by
    simpa [prefixWord, tailWord_4874008, baseEnd_4874008] using wordTrace_append hprefix tailTrace_4874008
  have hstable : (prefixWord ++ tailWord_4874008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874008).length < 2 ^ (prefixWord ++ tailWord_4874008).sum := by decide
  have hdescent : baseEnd_4874008 < baseStart_4874008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874015 : List Nat := [1, 1, 2, 4, 2, 1, 1, 5, 2, 4]
def baseStart_4874015 : Nat := 118140960795 + 4874015 * 2 ^ 59
def prefixEnd_4874015 : Nat := 4983230072969 + 3 ^ 40 * 4874015 * 2
def baseEnd_4874015 : Nat := 834237470741284375865773

theorem tailTrace_4874015 : CollatzResearch.WordTrace tailWord_4874015 prefixEnd_4874015 834237470741284375865773 := by
  unfold tailWord_4874015
  simp only [CollatzResearch.WordTrace]
  refine ⟨177769931437283545335127499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118513287624855696890084999 177769931437283545335127499)
  ·
    refine ⟨266654897155925318002691249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177769931437283545335127499 266654897155925318002691249)
    ·
      refine ⟨199991172866943988502018437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266654897155925318002691249 199991172866943988502018437)
      ·
        refine ⟨37498344912551997844128457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 199991172866943988502018437 37498344912551997844128457)
        ·
          refine ⟨28123758684413998383096343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37498344912551997844128457 28123758684413998383096343)
          ·
            refine ⟨42185638026620997574644515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28123758684413998383096343 42185638026620997574644515)
            ·
              refine ⟨63278457039931496361966773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42185638026620997574644515 63278457039931496361966773)
              ·
                refine ⟨5932355347493577783934385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63278457039931496361966773 5932355347493577783934385)
                ·
                  refine ⟨4449266510620183337950789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5932355347493577783934385 4449266510620183337950789)
                  ·
                    refine ⟨834237470741284375865773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449266510620183337950789 834237470741284375865773)
                    ·
                      rfl

theorem cell23_4874015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_4874015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874015 prefixEnd_4874015 := by exact prefixLift 4874015
  have htrace : WordTrace (prefixWord ++ tailWord_4874015) baseStart_4874015 baseEnd_4874015 := by
    simpa [prefixWord, tailWord_4874015, baseEnd_4874015] using wordTrace_append hprefix tailTrace_4874015
  have hstable : (prefixWord ++ tailWord_4874015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874015).length < 2 ^ (prefixWord ++ tailWord_4874015).sum := by decide
  have hdescent : baseEnd_4874015 < baseStart_4874015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874042 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3]
def baseStart_4874042 : Nat := 118140960795 + 4874042 * 2 ^ 59
def prefixEnd_4874042 : Nat := 4983230072969 + 3 ^ 40 * 4874042 * 2
def baseEnd_4874042 : Nat := 2502726276201524521959695

theorem tailTrace_4874042 : CollatzResearch.WordTrace tailWord_4874042 prefixEnd_4874042 2502726276201524521959695 := by
  unfold tailWord_4874042
  simp only [CollatzResearch.WordTrace]
  refine ⟨44442729052046432236590095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118513944138790485964240253 44442729052046432236590095)
  ·
    refine ⟨66664093578069648354885143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44442729052046432236590095 66664093578069648354885143)
    ·
      refine ⟨99996140367104472532327715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66664093578069648354885143 99996140367104472532327715)
      ·
        refine ⟨149994210550656708798491573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99996140367104472532327715 149994210550656708798491573)
        ·
          refine ⟨14061957239124066449858585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149994210550656708798491573 14061957239124066449858585)
          ·
            refine ⟨10546467929343049837393939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14061957239124066449858585 10546467929343049837393939)
            ·
              refine ⟨15819701894014574756090909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10546467929343049837393939 15819701894014574756090909)
              ·
                refine ⟨5932388210255465533534091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15819701894014574756090909 5932388210255465533534091)
                ·
                  refine ⟨8898582315383198300301137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5932388210255465533534091 8898582315383198300301137)
                  ·
                    refine ⟨6673936736537398725225853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8898582315383198300301137 6673936736537398725225853)
                    ·
                      refine ⟨2502726276201524521959695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6673936736537398725225853 2502726276201524521959695)
                      ·
                        rfl

theorem cell23_4874042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3].length) (baseStart_4874042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874042 prefixEnd_4874042 := by exact prefixLift 4874042
  have htrace : WordTrace (prefixWord ++ tailWord_4874042) baseStart_4874042 baseEnd_4874042 := by
    simpa [prefixWord, tailWord_4874042, baseEnd_4874042] using wordTrace_append hprefix tailTrace_4874042
  have hstable : (prefixWord ++ tailWord_4874042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874042).length < 2 ^ (prefixWord ++ tailWord_4874042).sum := by decide
  have hdescent : baseEnd_4874042 < baseStart_4874042 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874090 : List Nat := [3, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_4874090 : Nat := 118140960795 + 4874090 * 2 ^ 59
def prefixEnd_4874090 : Nat := 4983230072969 + 3 ^ 40 * 4874090 * 2
def baseEnd_4874090 : Nat := 2502750923272940334159475

theorem tailTrace_4874090 : CollatzResearch.WordTrace tailWord_4874090 prefixEnd_4874090 2502750923272940334159475 := by
  unfold tailWord_4874090
  simp only [CollatzResearch.WordTrace]
  refine ⟨44443166728002958286026931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118515111274674555429405149 44443166728002958286026931)
  ·
    refine ⟨66664750092004437429040397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44443166728002958286026931 66664750092004437429040397)
    ·
      refine ⟨24999281284501664035890149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66664750092004437429040397 24999281284501664035890149)
      ·
        refine ⟨4687365240844062006729403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24999281284501664035890149 4687365240844062006729403)
        ·
          refine ⟨7031047861266093010094105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687365240844062006729403 7031047861266093010094105)
          ·
            refine ⟨5273285895949569757570579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7031047861266093010094105 5273285895949569757570579)
            ·
              refine ⟨7909928843924354636355869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273285895949569757570579 7909928843924354636355869)
              ·
                refine ⟨2966223316471632988633451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7909928843924354636355869 2966223316471632988633451)
                ·
                  refine ⟨4449334974707449482950177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966223316471632988633451 4449334974707449482950177)
                  ·
                    refine ⟨3337001231030587112212633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449334974707449482950177 3337001231030587112212633)
                    ·
                      refine ⟨2502750923272940334159475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337001231030587112212633 2502750923272940334159475)
                      ·
                        rfl

theorem cell23_4874090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_4874090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874090 prefixEnd_4874090 := by exact prefixLift 4874090
  have htrace : WordTrace (prefixWord ++ tailWord_4874090) baseStart_4874090 baseEnd_4874090 := by
    simpa [prefixWord, tailWord_4874090, baseEnd_4874090] using wordTrace_append hprefix tailTrace_4874090
  have hstable : (prefixWord ++ tailWord_4874090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874090).length < 2 ^ (prefixWord ++ tailWord_4874090).sum := by decide
  have hdescent : baseEnd_4874090 < baseStart_4874090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874112 : List Nat := [2, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2]
def baseStart_4874112 : Nat := 118140960795 + 4874112 * 2 ^ 59
def prefixEnd_4874112 : Nat := 4983230072969 + 3 ^ 40 * 4874112 * 2
def baseEnd_4874112 : Nat := 2502762219847339248084373

theorem tailTrace_4874112 : CollatzResearch.WordTrace tailWord_4874112 prefixEnd_4874112 2502762219847339248084373 := by
  unfold tailWord_4874112
  simp only [CollatzResearch.WordTrace]
  refine ⟨88886734658966065450704295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118515646211954753934272393 88886734658966065450704295)
  ·
    refine ⟨133330101988449098176056443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88886734658966065450704295 133330101988449098176056443)
    ·
      refine ⟨199995152982673647264084665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133330101988449098176056443 199995152982673647264084665)
      ·
        refine ⟨149996364737005235448063499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199995152982673647264084665 149996364737005235448063499)
        ·
          refine ⟨224994547105507853172095249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149996364737005235448063499 224994547105507853172095249)
          ·
            refine ⟨168745910329130889879071437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224994547105507853172095249 168745910329130889879071437)
            ·
              refine ⟨63279716373424083704651789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168745910329130889879071437 63279716373424083704651789)
              ·
                refine ⟨23729893640034031389244421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63279716373424083704651789 23729893640034031389244421)
                ·
                  refine ⟨4449355057506380885483329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23729893640034031389244421 4449355057506380885483329)
                  ·
                    refine ⟨3337016293129785664112497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449355057506380885483329 3337016293129785664112497)
                    ·
                      refine ⟨2502762219847339248084373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337016293129785664112497 2502762219847339248084373)
                      ·
                        rfl

theorem cell23_4874112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 3, 4, 2, 2].length) (baseStart_4874112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874112 prefixEnd_4874112 := by exact prefixLift 4874112
  have htrace : WordTrace (prefixWord ++ tailWord_4874112) baseStart_4874112 baseEnd_4874112 := by
    simpa [prefixWord, tailWord_4874112, baseEnd_4874112] using wordTrace_append hprefix tailTrace_4874112
  have hstable : (prefixWord ++ tailWord_4874112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874112).length < 2 ^ (prefixWord ++ tailWord_4874112).sum := by decide
  have hdescent : baseEnd_4874112 < baseStart_4874112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874155 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 7, 2]
def baseStart_4874155 : Nat := 118140960795 + 4874155 * 2 ^ 59
def prefixEnd_4874155 : Nat := 4983230072969 + 3 ^ 40 * 4874155 * 2
def baseEnd_4874155 : Nat := 2502784299515482579846675

theorem tailTrace_4874155 : CollatzResearch.WordTrace tailWord_4874155 prefixEnd_4874155 2502784299515482579846675 := by
  unfold tailWord_4874155
  simp only [CollatzResearch.WordTrace]
  refine ⟨177775037656776349245223919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118516691771184232830149279 177775037656776349245223919)
  ·
    refine ⟨266662556485164523867835879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177775037656776349245223919 266662556485164523867835879)
    ·
      refine ⟨399993834727746785801753819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266662556485164523867835879 399993834727746785801753819)
      ·
        refine ⟨599990752091620178702630729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399993834727746785801753819 599990752091620178702630729)
        ·
          refine ⟨449993064068715134026973047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599990752091620178702630729 449993064068715134026973047)
          ·
            refine ⟨674989596103072701040459571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449993064068715134026973047 674989596103072701040459571)
            ·
              refine ⟨1012484394154609051560689357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674989596103072701040459571 1012484394154609051560689357)
              ·
                refine ⟨379681647807978394335258509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1012484394154609051560689357 379681647807978394335258509)
                ·
                  refine ⟨142380617927991897875721941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379681647807978394335258509 142380617927991897875721941)
                  ·
                    refine ⟨3337045732687310106462233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142380617927991897875721941 3337045732687310106462233)
                    ·
                      refine ⟨2502784299515482579846675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337045732687310106462233 2502784299515482579846675)
                      ·
                        rfl

theorem cell23_4874155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 7, 2].length) (baseStart_4874155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874155 prefixEnd_4874155 := by exact prefixLift 4874155
  have htrace : WordTrace (prefixWord ++ tailWord_4874155) baseStart_4874155 baseEnd_4874155 := by
    simpa [prefixWord, tailWord_4874155, baseEnd_4874155] using wordTrace_append hprefix tailTrace_4874155
  have hstable : (prefixWord ++ tailWord_4874155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874155).length < 2 ^ (prefixWord ++ tailWord_4874155).sum := by decide
  have hdescent : baseEnd_4874155 < baseStart_4874155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874202 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_4874202 : Nat := 118140960795 + 4874202 * 2 ^ 59
def prefixEnd_4874202 : Nat := 4983230072969 + 3 ^ 40 * 4874202 * 2
def baseEnd_4874202 : Nat := 2502808433106243895958959

theorem tailTrace_4874202 : CollatzResearch.WordTrace tailWord_4874202 prefixEnd_4874202 2502808433106243895958959 := by
  unfold tailWord_4874202
  simp only [CollatzResearch.WordTrace]
  refine ⟨44444187971901519068046215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118517834591737384181456573 44444187971901519068046215)
  ·
    refine ⟨66666281957852278602069323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44444187971901519068046215 66666281957852278602069323)
    ·
      refine ⟨99999422936778417903103985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66666281957852278602069323 99999422936778417903103985)
      ·
        refine ⟨74999567202583813427327989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99999422936778417903103985 74999567202583813427327989)
        ·
          refine ⟨7031209425242232508811999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74999567202583813427327989 7031209425242232508811999)
          ·
            refine ⟨10546814137863348763217999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7031209425242232508811999 10546814137863348763217999)
            ·
              refine ⟨15820221206795023144826999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10546814137863348763217999 15820221206795023144826999)
              ·
                refine ⟨23730331810192534717240499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15820221206795023144826999 23730331810192534717240499)
                ·
                  refine ⟨35595497715288802075860749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23730331810192534717240499 35595497715288802075860749)
                  ·
                    refine ⟨13348311643233300778447781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35595497715288802075860749 13348311643233300778447781)
                    ·
                      refine ⟨2502808433106243895958959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13348311643233300778447781 2502808433106243895958959)
                      ·
                        rfl

theorem cell23_4874202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_4874202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874202 prefixEnd_4874202 := by exact prefixLift 4874202
  have htrace : WordTrace (prefixWord ++ tailWord_4874202) baseStart_4874202 baseEnd_4874202 := by
    simpa [prefixWord, tailWord_4874202, baseEnd_4874202] using wordTrace_append hprefix tailTrace_4874202
  have hstable : (prefixWord ++ tailWord_4874202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874202).length < 2 ^ (prefixWord ++ tailWord_4874202).sum := by decide
  have hdescent : baseEnd_4874202 < baseStart_4874202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874263 : List Nat := [1, 1, 3, 5, 2, 2, 1, 3, 1, 4]
def baseStart_4874263 : Nat := 118140960795 + 4874263 * 2 ^ 59
def prefixEnd_4874263 : Nat := 4983230072969 + 3 ^ 40 * 4874263 * 2
def baseEnd_4874263 : Nat := 834279918475389385765393

theorem tailTrace_4874263 : CollatzResearch.WordTrace tailWord_4874263 prefixEnd_4874263 834279918475389385765393 := by
  unfold tailWord_4874263
  simp only [CollatzResearch.WordTrace]
  refine ⟨177778976740385083690155443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118519317826923389126770295 177778976740385083690155443)
  ·
    refine ⟨266668465110577625535233165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177778976740385083690155443 266668465110577625535233165)
    ·
      refine ⟨100000674416466609575712437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266668465110577625535233165 100000674416466609575712437)
      ·
        refine ⟨9375063226543744647723041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100000674416466609575712437 9375063226543744647723041)
        ·
          refine ⟨7031297419907808485792281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9375063226543744647723041 7031297419907808485792281)
          ·
            refine ⟨5273473064930856364344211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7031297419907808485792281 5273473064930856364344211)
            ·
              refine ⟨7910209597396284546516317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273473064930856364344211 7910209597396284546516317)
              ·
                refine ⟨2966328599023606704943619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7910209597396284546516317 2966328599023606704943619)
                ·
                  refine ⟨4449492898535410057415429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966328599023606704943619 4449492898535410057415429)
                  ·
                    refine ⟨834279918475389385765393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449492898535410057415429 834279918475389385765393)
                    ·
                      rfl

theorem cell23_4874263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_4874263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874263 prefixEnd_4874263 := by exact prefixLift 4874263
  have htrace : WordTrace (prefixWord ++ tailWord_4874263) baseStart_4874263 baseEnd_4874263 := by
    simpa [prefixWord, tailWord_4874263, baseEnd_4874263] using wordTrace_append hprefix tailTrace_4874263
  have hstable : (prefixWord ++ tailWord_4874263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874263).length < 2 ^ (prefixWord ++ tailWord_4874263).sum := by decide
  have hdescent : baseEnd_4874263 < baseStart_4874263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874280 : List Nat := [2, 1, 5, 3, 1, 1, 3, 2, 1, 4]
def baseStart_4874280 : Nat := 118140960795 + 4874280 * 2 ^ 59
def prefixEnd_4874280 : Nat := 4983230072969 + 3 ^ 40 * 4874280 * 2
def baseEnd_4874280 : Nat := 834282828199098196927867

theorem tailTrace_4874280 : CollatzResearch.WordTrace tailWord_4874280 prefixEnd_4874280 834282828199098196927867 := by
  unfold tailWord_4874280
  simp only [CollatzResearch.WordTrace]
  refine ⟨88889798390661747796762147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118519731187548997062349529 88889798390661747796762147)
  ·
    refine ⟨133334697585992621695143221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88889798390661747796762147 133334697585992621695143221)
    ·
      refine ⟨12500127898686808283919677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133334697585992621695143221 12500127898686808283919677)
      ·
        refine ⟨4687547962007553106469879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12500127898686808283919677 4687547962007553106469879)
        ·
          refine ⟨7031321943011329659704819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4687547962007553106469879 7031321943011329659704819)
          ·
            refine ⟨10546982914516994489557229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7031321943011329659704819 10546982914516994489557229)
            ·
              refine ⟨3955118592943872933583961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10546982914516994489557229 3955118592943872933583961)
              ·
                refine ⟨2966338944707904700187971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955118592943872933583961 2966338944707904700187971)
                ·
                  refine ⟨4449508417061857050281957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966338944707904700187971 4449508417061857050281957)
                  ·
                    refine ⟨834282828199098196927867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4449508417061857050281957 834282828199098196927867)
                    ·
                      rfl

theorem cell23_4874280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_4874280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874280 prefixEnd_4874280 := by exact prefixLift 4874280
  have htrace : WordTrace (prefixWord ++ tailWord_4874280) baseStart_4874280 baseEnd_4874280 := by
    simpa [prefixWord, tailWord_4874280, baseEnd_4874280] using wordTrace_append hprefix tailTrace_4874280
  have hstable : (prefixWord ++ tailWord_4874280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874280).length < 2 ^ (prefixWord ++ tailWord_4874280).sum := by decide
  have hdescent : baseEnd_4874280 < baseStart_4874280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874286 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_4874286 : Nat := 118140960795 + 4874286 * 2 ^ 59
def prefixEnd_4874286 : Nat := 4983230072969 + 3 ^ 40 * 4874286 * 2
def baseEnd_4874286 : Nat := 2502851565481221567308573

theorem tailTrace_4874286 : CollatzResearch.WordTrace tailWord_4874286 prefixEnd_4874286 2502851565481221567308573 := by
  unfold tailWord_4874286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22222476952412719827280339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118519877079534505745495141 22222476952412719827280339)
  ·
    refine ⟨33333715428619079740920509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22222476952412719827280339 33333715428619079740920509)
    ·
      refine ⟨12500143285732154902845191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33333715428619079740920509 12500143285732154902845191)
      ·
        refine ⟨18750214928598232354267787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12500143285732154902845191 18750214928598232354267787)
        ·
          refine ⟨28125322392897348531401681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18750214928598232354267787 28125322392897348531401681)
          ·
            refine ⟨21093991794673011398551261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28125322392897348531401681 21093991794673011398551261)
            ·
              refine ⟨7910246923002379274456723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21093991794673011398551261 7910246923002379274456723)
              ·
                refine ⟨11865370384503568911685085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910246923002379274456723 11865370384503568911685085)
                ·
                  refine ⟨4449513894188838341881907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11865370384503568911685085 4449513894188838341881907)
                  ·
                    refine ⟨6674270841283257512822861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4449513894188838341881907 6674270841283257512822861)
                    ·
                      refine ⟨2502851565481221567308573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674270841283257512822861 2502851565481221567308573)
                      ·
                        rfl

theorem cell23_4874286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_4874286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874286 prefixEnd_4874286 := by exact prefixLift 4874286
  have htrace : WordTrace (prefixWord ++ tailWord_4874286) baseStart_4874286 baseEnd_4874286 := by
    simpa [prefixWord, tailWord_4874286, baseEnd_4874286] using wordTrace_append hprefix tailTrace_4874286
  have hstable : (prefixWord ++ tailWord_4874286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874286).length < 2 ^ (prefixWord ++ tailWord_4874286).sum := by decide
  have hdescent : baseEnd_4874286 < baseStart_4874286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874309 : List Nat := [1, 3, 1, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_4874309 : Nat := 118140960795 + 4874309 * 2 ^ 59
def prefixEnd_4874309 : Nat := 4983230072969 + 3 ^ 40 * 4874309 * 2
def baseEnd_4874309 : Nat := 2502863375536274977320967

theorem tailTrace_4874309 : CollatzResearch.WordTrace tailWord_4874309 prefixEnd_4874309 2502863375536274977320967 := by
  unfold tailWord_4874309
  simp only [CollatzResearch.WordTrace]
  refine ⟨177780654498218433546329981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118520436332145622364219987 177780654498218433546329981)
  ·
    refine ⟨66667745436831912579873743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177780654498218433546329981 66667745436831912579873743)
    ·
      refine ⟨100001618155247868869810615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66667745436831912579873743 100001618155247868869810615)
      ·
        refine ⟨150002427232871803304715923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100001618155247868869810615 150002427232871803304715923)
        ·
          refine ⟨225003640849307704957073885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150002427232871803304715923 225003640849307704957073885)
          ·
            refine ⟨84376365318490389358902707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225003640849307704957073885 84376365318490389358902707)
            ·
              refine ⟨126564547977735584038354061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84376365318490389358902707 126564547977735584038354061)
              ·
                refine ⟨47461705491650844014382773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126564547977735584038354061 47461705491650844014382773)
                ·
                  refine ⟨4449534889842266626348385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47461705491650844014382773 4449534889842266626348385)
                  ·
                    refine ⟨3337151167381699969761289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449534889842266626348385 3337151167381699969761289)
                    ·
                      refine ⟨2502863375536274977320967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337151167381699969761289 2502863375536274977320967)
                      ·
                        rfl

theorem cell23_4874309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_4874309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874309 prefixEnd_4874309 := by exact prefixLift 4874309
  have htrace : WordTrace (prefixWord ++ tailWord_4874309) baseStart_4874309 baseEnd_4874309 := by
    simpa [prefixWord, tailWord_4874309, baseEnd_4874309] using wordTrace_append hprefix tailTrace_4874309
  have hstable : (prefixWord ++ tailWord_4874309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874309).length < 2 ^ (prefixWord ++ tailWord_4874309).sum := by decide
  have hdescent : baseEnd_4874309 < baseStart_4874309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874335 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_4874335 : Nat := 118140960795 + 4874335 * 2 ^ 59
def prefixEnd_4874335 : Nat := 4983230072969 + 3 ^ 40 * 4874335 * 2
def baseEnd_4874335 : Nat := 2502876726033291875595847

theorem tailTrace_4874335 : CollatzResearch.WordTrace tailWord_4874335 prefixEnd_4874335 2502876726033291875595847 := by
  unfold tailWord_4874335
  simp only [CollatzResearch.WordTrace]
  refine ⟨177781602796124239986776459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118521068530749493324517639 177781602796124239986776459)
  ·
    refine ⟨266672404194186359980164689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177781602796124239986776459 266672404194186359980164689)
    ·
      refine ⟨200004303145639769985123517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266672404194186359980164689 200004303145639769985123517)
      ·
        refine ⟨75001613679614913744421319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200004303145639769985123517 75001613679614913744421319)
        ·
          refine ⟨112502420519422370616631979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75001613679614913744421319 112502420519422370616631979)
          ·
            refine ⟨168753630779133555924947969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112502420519422370616631979 168753630779133555924947969)
            ·
              refine ⟨126565223084350166943710977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168753630779133555924947969 126565223084350166943710977)
              ·
                refine ⟨94923917313262625207783233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126565223084350166943710977 94923917313262625207783233)
                ·
                  refine ⟨71192937984946968905837425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94923917313262625207783233 71192937984946968905837425)
                  ·
                    refine ⟨53394703488710226679378069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71192937984946968905837425 53394703488710226679378069)
                    ·
                      refine ⟨2502876726033291875595847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53394703488710226679378069 2502876726033291875595847)
                      ·
                        rfl

theorem cell23_4874335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_4874335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874335 prefixEnd_4874335 := by exact prefixLift 4874335
  have htrace : WordTrace (prefixWord ++ tailWord_4874335) baseStart_4874335 baseEnd_4874335 := by
    simpa [prefixWord, tailWord_4874335, baseEnd_4874335] using wordTrace_append hprefix tailTrace_4874335
  have hstable : (prefixWord ++ tailWord_4874335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874335).length < 2 ^ (prefixWord ++ tailWord_4874335).sum := by decide
  have hdescent : baseEnd_4874335 < baseStart_4874335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874343 : List Nat := [1, 1, 5, 1, 1, 2, 3, 4, 1, 2, 2]
def baseStart_4874343 : Nat := 118140960795 + 4874343 * 2 ^ 59
def prefixEnd_4874343 : Nat := 4983230072969 + 3 ^ 40 * 4874343 * 2
def baseEnd_4874343 : Nat := 2502880833878527844295811

theorem tailTrace_4874343 : CollatzResearch.WordTrace tailWord_4874343 prefixEnd_4874343 2502880833878527844295811 := by
  unfold tailWord_4874343
  simp only [CollatzResearch.WordTrace]
  refine ⟨177781894580095257353067683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118521263053396838235378455 177781894580095257353067683)
  ·
    refine ⟨266672841870142886029601525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177781894580095257353067683 266672841870142886029601525)
    ·
      refine ⟨25000578925325895565275143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266672841870142886029601525 25000578925325895565275143)
      ·
        refine ⟨37500868387988843347912715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25000578925325895565275143 37500868387988843347912715)
        ·
          refine ⟨56251302581983265021869073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37500868387988843347912715 56251302581983265021869073)
          ·
            refine ⟨42188476936487448766401805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56251302581983265021869073 42188476936487448766401805)
            ·
              refine ⟨15820678851182793287400677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42188476936487448766401805 15820678851182793287400677)
              ·
                refine ⟨2966377284596773741387627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15820678851182793287400677 2966377284596773741387627)
                ·
                  refine ⟨4449565926895160612081441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966377284596773741387627 4449565926895160612081441)
                  ·
                    refine ⟨3337174445171370459061081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449565926895160612081441 3337174445171370459061081)
                    ·
                      refine ⟨2502880833878527844295811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337174445171370459061081 2502880833878527844295811)
                      ·
                        rfl

theorem cell23_4874343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_4874343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874343 prefixEnd_4874343 := by exact prefixLift 4874343
  have htrace : WordTrace (prefixWord ++ tailWord_4874343) baseStart_4874343 baseEnd_4874343 := by
    simpa [prefixWord, tailWord_4874343, baseEnd_4874343] using wordTrace_append hprefix tailTrace_4874343
  have hstable : (prefixWord ++ tailWord_4874343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874343).length < 2 ^ (prefixWord ++ tailWord_4874343).sum := by decide
  have hdescent : baseEnd_4874343 < baseStart_4874343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874345 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 1, 9]
def baseStart_4874345 : Nat := 118140960795 + 4874345 * 2 ^ 59
def prefixEnd_4874345 : Nat := 4983230072969 + 3 ^ 40 * 4874345 * 2
def baseEnd_4874345 : Nat := 834293953613278945490267

theorem tailTrace_4874345 : CollatzResearch.WordTrace tailWord_4874345 prefixEnd_4874345 834293953613278945490267 := by
  unfold tailWord_4874345
  simp only [CollatzResearch.WordTrace]
  refine ⟨177781967526088011694640489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118521311684058674463093659 177781967526088011694640489)
  ·
    refine ⟨133336475644566008770980367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177781967526088011694640489 133336475644566008770980367)
    ·
      refine ⟨200004713466849013156470551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133336475644566008770980367 200004713466849013156470551)
      ·
        refine ⟨300007070200273519734705827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200004713466849013156470551 300007070200273519734705827)
        ·
          refine ⟨450010605300410279602058741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300007070200273519734705827 450010605300410279602058741)
          ·
            refine ⟨42188494246913463712693007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 450010605300410279602058741 42188494246913463712693007)
            ·
              refine ⟨63282741370370195569039511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42188494246913463712693007 63282741370370195569039511)
              ·
                refine ⟨94924112055555293353559267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63282741370370195569039511 94924112055555293353559267)
                ·
                  refine ⟨142386168083332940030338901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94924112055555293353559267 142386168083332940030338901)
                  ·
                    refine ⟨834293953613278945490267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 142386168083332940030338901 834293953613278945490267)
                    ·
                      rfl

theorem cell23_4874345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 1, 9].length) (baseStart_4874345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874345 prefixEnd_4874345 := by exact prefixLift 4874345
  have htrace : WordTrace (prefixWord ++ tailWord_4874345) baseStart_4874345 baseEnd_4874345 := by
    simpa [prefixWord, tailWord_4874345, baseEnd_4874345] using wordTrace_append hprefix tailTrace_4874345
  have hstable : (prefixWord ++ tailWord_4874345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874345).length < 2 ^ (prefixWord ++ tailWord_4874345).sum := by decide
  have hdescent : baseEnd_4874345 < baseStart_4874345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874359 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3]
def baseStart_4874359 : Nat := 118140960795 + 4874359 * 2 ^ 59
def prefixEnd_4874359 : Nat := 4983230072969 + 3 ^ 40 * 4874359 * 2
def baseEnd_4874359 : Nat := 2502889049568999781695737

theorem tailTrace_4874359 : CollatzResearch.WordTrace tailWord_4874359 prefixEnd_4874359 2502889049568999781695737 := by
  unfold tailWord_4874359
  simp only [CollatzResearch.WordTrace]
  refine ⟨177782478148037292085650131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118521652098691528057100087 177782478148037292085650131)
  ·
    refine ⟨266673717222055938128475197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177782478148037292085650131 266673717222055938128475197)
    ·
      refine ⟨100002643958270976798178199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266673717222055938128475197 100002643958270976798178199)
      ·
        refine ⟨150003965937406465197267299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100002643958270976798178199 150003965937406465197267299)
        ·
          refine ⟨225005948906109697795900949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150003965937406465197267299 225005948906109697795900949)
          ·
            refine ⟨10547153854973892084182857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 225005948906109697795900949 10547153854973892084182857)
            ·
              refine ⟨7910365391230419063137143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10547153854973892084182857 7910365391230419063137143)
              ·
                refine ⟨11865548086845628594705715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910365391230419063137143 11865548086845628594705715)
                ·
                  refine ⟨17798322130268442892058573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11865548086845628594705715 17798322130268442892058573)
                  ·
                    refine ⟨6674370798850666084521965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17798322130268442892058573 6674370798850666084521965)
                    ·
                      refine ⟨2502889049568999781695737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674370798850666084521965 2502889049568999781695737)
                      ·
                        rfl

theorem cell23_4874359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3, 3].length) (baseStart_4874359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874359 prefixEnd_4874359 := by exact prefixLift 4874359
  have htrace : WordTrace (prefixWord ++ tailWord_4874359) baseStart_4874359 baseEnd_4874359 := by
    simpa [prefixWord, tailWord_4874359, baseEnd_4874359] using wordTrace_append hprefix tailTrace_4874359
  have hstable : (prefixWord ++ tailWord_4874359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874359).length < 2 ^ (prefixWord ++ tailWord_4874359).sum := by decide
  have hdescent : baseEnd_4874359 < baseStart_4874359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874372 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_4874372 : Nat := 118140960795 + 4874372 * 2 ^ 59
def prefixEnd_4874372 : Nat := 4983230072969 + 3 ^ 40 * 4874372 * 2
def baseEnd_4874372 : Nat := 2502895724817508230833177

theorem tailTrace_4874372 : CollatzResearch.WordTrace tailWord_4874372 prefixEnd_4874372 2502895724817508230833177 := by
  unfold tailWord_4874372
  simp only [CollatzResearch.WordTrace]
  refine ⟨88891476148495097652936685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118521968197993463537248913 88891476148495097652936685)
  ·
    refine ⟨33334303555685661619851257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88891476148495097652936685 33334303555685661619851257)
    ·
      refine ⟨25000727666764246214888443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33334303555685661619851257 25000727666764246214888443)
      ·
        refine ⟨37501091500146369322332665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25000727666764246214888443 37501091500146369322332665)
        ·
          refine ⟨28125818625109776991749499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37501091500146369322332665 28125818625109776991749499)
          ·
            refine ⟨42188727937664665487624249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28125818625109776991749499 42188727937664665487624249)
            ·
              refine ⟨31641545953248499115718187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42188727937664665487624249 31641545953248499115718187)
              ·
                refine ⟨47462318929872748673577281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31641545953248499115718187 47462318929872748673577281)
                ·
                  refine ⟨35596739197404561505182961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47462318929872748673577281 35596739197404561505182961)
                  ·
                    refine ⟨26697554398053421128887221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35596739197404561505182961 26697554398053421128887221)
                    ·
                      refine ⟨2502895724817508230833177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26697554398053421128887221 2502895724817508230833177)
                      ·
                        rfl

theorem cell23_4874372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_4874372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874372 prefixEnd_4874372 := by exact prefixLift 4874372
  have htrace : WordTrace (prefixWord ++ tailWord_4874372) baseStart_4874372 baseEnd_4874372 := by
    simpa [prefixWord, tailWord_4874372, baseEnd_4874372] using wordTrace_append hprefix tailTrace_4874372
  have hstable : (prefixWord ++ tailWord_4874372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874372).length < 2 ^ (prefixWord ++ tailWord_4874372).sum := by decide
  have hdescent : baseEnd_4874372 < baseStart_4874372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874410 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_4874410 : Nat := 118140960795 + 4874410 * 2 ^ 59
def prefixEnd_4874410 : Nat := 4983230072969 + 3 ^ 40 * 4874410 * 2
def baseEnd_4874410 : Nat := 2502915237082379082158003

theorem tailTrace_4874410 : CollatzResearch.WordTrace tailWord_4874410 prefixEnd_4874410 2502915237082379082158003 := by
  unfold tailWord_4874410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44446084567713131948939171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118522892180568351863837789 44446084567713131948939171)
  ·
    refine ⟨66669126851569697923408757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44446084567713131948939171 66669126851569697923408757)
    ·
      refine ⟨6250230642334659180319571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66669126851569697923408757 6250230642334659180319571)
      ·
        refine ⟨9375345963501988770479357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250230642334659180319571 9375345963501988770479357)
        ·
          refine ⟨3515754736313245788929759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9375345963501988770479357 3515754736313245788929759)
          ·
            refine ⟨5273632104469868683394639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3515754736313245788929759 5273632104469868683394639)
            ·
              refine ⟨7910448156704803025091959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273632104469868683394639 7910448156704803025091959)
              ·
                refine ⟨11865672235057204537637939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7910448156704803025091959 11865672235057204537637939)
                ·
                  refine ⟨17798508352585806806456909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11865672235057204537637939 17798508352585806806456909)
                  ·
                    refine ⟨6674440632219677552421341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17798508352585806806456909 6674440632219677552421341)
                    ·
                      refine ⟨2502915237082379082158003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674440632219677552421341 2502915237082379082158003)
                      ·
                        rfl

theorem cell23_4874410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_4874410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874410 prefixEnd_4874410 := by exact prefixLift 4874410
  have htrace : WordTrace (prefixWord ++ tailWord_4874410) baseStart_4874410 baseEnd_4874410 := by
    simpa [prefixWord, tailWord_4874410, baseEnd_4874410] using wordTrace_append hprefix tailTrace_4874410
  have hstable : (prefixWord ++ tailWord_4874410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874410).length < 2 ^ (prefixWord ++ tailWord_4874410).sum := by decide
  have hdescent : baseEnd_4874410 < baseStart_4874410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874489 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 6, 2]
def baseStart_4874489 : Nat := 118140960795 + 4874489 * 2 ^ 59
def prefixEnd_4874489 : Nat := 4983230072969 + 3 ^ 40 * 4874489 * 2
def baseEnd_4874489 : Nat := 2502955802054084273070139

theorem tailTrace_4874489 : CollatzResearch.WordTrace tailWord_4874489 prefixEnd_4874489 2502955802054084273070139 := by
  unfold tailWord_4874489
  simp only [CollatzResearch.WordTrace]
  refine ⟨177787219637566324287882521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118524813091710882858588347 177787219637566324287882521)
  ·
    refine ⟨133340414728174743215911891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177787219637566324287882521 133340414728174743215911891)
    ·
      refine ⟨200010622092262114823867837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133340414728174743215911891 200010622092262114823867837)
      ·
        refine ⟨75003983284598293058950439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200010622092262114823867837 75003983284598293058950439)
        ·
          refine ⟨112505974926897439588425659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75003983284598293058950439 112505974926897439588425659)
          ·
            refine ⟨168758962390346159382638489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112505974926897439588425659 168758962390346159382638489)
            ·
              refine ⟨126569221792759619536978867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168758962390346159382638489 126569221792759619536978867)
              ·
                refine ⟨189853832689139429305468301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126569221792759619536978867 189853832689139429305468301)
                ·
                  refine ⟨71195187258427285989550613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 189853832689139429305468301 71195187258427285989550613)
                  ·
                    refine ⟨3337274402738779030760185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71195187258427285989550613 3337274402738779030760185)
                    ·
                      refine ⟨2502955802054084273070139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337274402738779030760185 2502955802054084273070139)
                      ·
                        rfl

theorem cell23_4874489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 6, 2].length) (baseStart_4874489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874489 prefixEnd_4874489 := by exact prefixLift 4874489
  have htrace : WordTrace (prefixWord ++ tailWord_4874489) baseStart_4874489 baseEnd_4874489 := by
    simpa [prefixWord, tailWord_4874489, baseEnd_4874489] using wordTrace_append hprefix tailTrace_4874489
  have hstable : (prefixWord ++ tailWord_4874489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874489).length < 2 ^ (prefixWord ++ tailWord_4874489).sum := by decide
  have hdescent : baseEnd_4874489 < baseStart_4874489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874529 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 6]
def baseStart_4874529 : Nat := 118140960795 + 4874529 * 2 ^ 59
def prefixEnd_4874529 : Nat := 4983230072969 + 3 ^ 40 * 4874529 * 2
def baseEnd_4874529 : Nat := 278108482364473790729995

theorem tailTrace_4874529 : CollatzResearch.WordTrace tailWord_4874529 prefixEnd_4874529 278108482364473790729995 := by
  unfold tailWord_4874529
  simp only [CollatzResearch.WordTrace]
  refine ⟨177788678557421411119338641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118525785704947607412892427 177788678557421411119338641)
  ·
    refine ⟨133341508918066058339503981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177788678557421411119338641 133341508918066058339503981)
    ·
      refine ⟨50003065844274771877313993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133341508918066058339503981 50003065844274771877313993)
      ·
        refine ⟨37502299383206078907985495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50003065844274771877313993 37502299383206078907985495)
        ·
          refine ⟨56253449074809118361978243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37502299383206078907985495 56253449074809118361978243)
          ·
            refine ⟨84380173612213677542967365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56253449074809118361978243 84380173612213677542967365)
            ·
              refine ⟨15821282552290064539306381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84380173612213677542967365 15821282552290064539306381)
              ·
                refine ⟨5932980957108774202239893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15821282552290064539306381 5932980957108774202239893)
                ·
                  refine ⟨278108482364473790729995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5932980957108774202239893 278108482364473790729995)
                  ·
                    rfl

theorem cell23_4874529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 6].length) (baseStart_4874529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874529 prefixEnd_4874529 := by exact prefixLift 4874529
  have htrace : WordTrace (prefixWord ++ tailWord_4874529) baseStart_4874529 baseEnd_4874529 := by
    simpa [prefixWord, tailWord_4874529, baseEnd_4874529] using wordTrace_append hprefix tailTrace_4874529
  have hstable : (prefixWord ++ tailWord_4874529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874529).length < 2 ^ (prefixWord ++ tailWord_4874529).sum := by decide
  have hdescent : baseEnd_4874529 < baseStart_4874529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874556 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_4874556 : Nat := 118140960795 + 4874556 * 2 ^ 59
def prefixEnd_4874556 : Nat := 4983230072969 + 3 ^ 40 * 4874556 * 2
def baseEnd_4874556 : Nat := 2502990205257935510932331

theorem tailTrace_4874556 : CollatzResearch.WordTrace tailWord_4874556 prefixEnd_4874556 2502990205257935510932331 := by
  unfold tailWord_4874556
  simp only [CollatzResearch.WordTrace]
  refine ⟨88894831664161797365285761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118526442218882396487047681 88894831664161797365285761)
  ·
    refine ⟨66671123748121348023964321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88894831664161797365285761 66671123748121348023964321)
    ·
      refine ⟨50003342811091011017973241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66671123748121348023964321 50003342811091011017973241)
      ·
        refine ⟨37502507108318258263479931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50003342811091011017973241 37502507108318258263479931)
        ·
          refine ⟨56253760662477387395219897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37502507108318258263479931 56253760662477387395219897)
          ·
            refine ⟨42190320496858040546414923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56253760662477387395219897 42190320496858040546414923)
            ·
              refine ⟨63285480745287060819622385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42190320496858040546414923 63285480745287060819622385)
              ·
                refine ⟨47464110558965295614716789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63285480745287060819622385 47464110558965295614716789)
                ·
                  refine ⟨4449760364902996463879699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47464110558965295614716789 4449760364902996463879699)
                  ·
                    refine ⟨6674640547354494695819549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4449760364902996463879699 6674640547354494695819549)
                    ·
                      refine ⟨2502990205257935510932331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674640547354494695819549 2502990205257935510932331)
                      ·
                        rfl

theorem cell23_4874556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_4874556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874556 prefixEnd_4874556 := by exact prefixLift 4874556
  have htrace : WordTrace (prefixWord ++ tailWord_4874556) baseStart_4874556 baseEnd_4874556 := by
    simpa [prefixWord, tailWord_4874556, baseEnd_4874556] using wordTrace_append hprefix tailTrace_4874556
  have hstable : (prefixWord ++ tailWord_4874556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874556).length < 2 ^ (prefixWord ++ tailWord_4874556).sum := by decide
  have hdescent : baseEnd_4874556 < baseStart_4874556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874579 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4]
def baseStart_4874579 : Nat := 118140960795 + 4874579 * 2 ^ 59
def prefixEnd_4874579 : Nat := 4983230072969 + 3 ^ 40 * 4874579 * 2
def baseEnd_4874579 : Nat := 2503002015312988920944725

theorem tailTrace_4874579 : CollatzResearch.WordTrace tailWord_4874579 prefixEnd_4874579 2503002015312988920944725 := by
  unfold tailWord_4874579
  simp only [CollatzResearch.WordTrace]
  refine ⟨177790502207240269658658791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118527001471493513105772527 177790502207240269658658791)
  ·
    refine ⟨266685753310860404487988187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177790502207240269658658791 266685753310860404487988187)
    ·
      refine ⟨400028629966290606731982281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266685753310860404487988187 400028629966290606731982281)
      ·
        refine ⟨300021472474717955048986711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400028629966290606731982281 300021472474717955048986711)
        ·
          refine ⟨450032208712076932573480067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300021472474717955048986711 450032208712076932573480067)
          ·
            refine ⟨675048313068115398860220101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450032208712076932573480067 675048313068115398860220101)
            ·
              refine ⟨126571558700271637286291269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 675048313068115398860220101 126571558700271637286291269)
              ·
                refine ⟨23732167256300931991179613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126571558700271637286291269 23732167256300931991179613)
                ·
                  refine ⟨8899562721112849496692355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23732167256300931991179613 8899562721112849496692355)
                  ·
                    refine ⟨13349344081669274245038533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8899562721112849496692355 13349344081669274245038533)
                    ·
                      refine ⟨2503002015312988920944725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13349344081669274245038533 2503002015312988920944725)
                      ·
                        rfl

theorem cell23_4874579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_4874579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874579 prefixEnd_4874579 := by exact prefixLift 4874579
  have htrace : WordTrace (prefixWord ++ tailWord_4874579) baseStart_4874579 baseEnd_4874579 := by
    simpa [prefixWord, tailWord_4874579, baseEnd_4874579] using wordTrace_append hprefix tailTrace_4874579
  have hstable : (prefixWord ++ tailWord_4874579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874579).length < 2 ^ (prefixWord ++ tailWord_4874579).sum := by decide
  have hdescent : baseEnd_4874579 < baseStart_4874579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874596 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 6, 2]
def baseStart_4874596 : Nat := 118140960795 + 4874596 * 2 ^ 59
def prefixEnd_4874596 : Nat := 4983230072969 + 3 ^ 40 * 4874596 * 2
def baseEnd_4874596 : Nat := 2503010744484115354432147

theorem tailTrace_4874596 : CollatzResearch.WordTrace tailWord_4874596 prefixEnd_4874596 2503010744484115354432147 := by
  unfold tailWord_4874596
  simp only [CollatzResearch.WordTrace]
  refine ⟨88895561124089340781013821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118527414832119121041351761 88895561124089340781013821)
  ·
    refine ⟨33335835421533502792880183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88895561124089340781013821 33335835421533502792880183)
    ·
      refine ⟨50003753132300254189320275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33335835421533502792880183 50003753132300254189320275)
      ·
        refine ⟨75005629698450381283980413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50003753132300254189320275 75005629698450381283980413)
        ·
          refine ⟨28127111136918892981492655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75005629698450381283980413 28127111136918892981492655)
          ·
            refine ⟨42190666705378339472238983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28127111136918892981492655 42190666705378339472238983)
            ·
              refine ⟨63286000058067509208358475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42190666705378339472238983 63286000058067509208358475)
              ·
                refine ⟨94929000087101263812537713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63286000058067509208358475 94929000087101263812537713)
                ·
                  refine ⟨71196750065325947859403285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94929000087101263812537713 71196750065325947859403285)
                  ·
                    refine ⟨3337347659312153805909529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71196750065325947859403285 3337347659312153805909529)
                    ·
                      refine ⟨2503010744484115354432147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337347659312153805909529 2503010744484115354432147)
                      ·
                        rfl

theorem cell23_4874596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_4874596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874596 prefixEnd_4874596 := by exact prefixLift 4874596
  have htrace : WordTrace (prefixWord ++ tailWord_4874596) baseStart_4874596 baseEnd_4874596 := by
    simpa [prefixWord, tailWord_4874596, baseEnd_4874596] using wordTrace_append hprefix tailTrace_4874596
  have hstable : (prefixWord ++ tailWord_4874596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874596).length < 2 ^ (prefixWord ++ tailWord_4874596).sum := by decide
  have hdescent : baseEnd_4874596 < baseStart_4874596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874609 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_4874609 : Nat := 118140960795 + 4874609 * 2 ^ 59
def prefixEnd_4874609 : Nat := 4983230072969 + 3 ^ 40 * 4874609 * 2
def baseEnd_4874609 : Nat := 2503017419732623803569587

theorem tailTrace_4874609 : CollatzResearch.WordTrace tailWord_4874609 prefixEnd_4874609 2503017419732623803569587 := by
  unfold tailWord_4874609
  simp only [CollatzResearch.WordTrace]
  refine ⟨177791596397131584782250881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118527730931421056521500587 177791596397131584782250881)
  ·
    refine ⟨133343697297848688586688161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177791596397131584782250881 133343697297848688586688161)
    ·
      refine ⟨100007772973386516440016121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133343697297848688586688161 100007772973386516440016121)
      ·
        refine ⟨75005829730039887330012091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100007772973386516440016121 75005829730039887330012091)
        ·
          refine ⟨112508744595059830995018137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75005829730039887330012091 112508744595059830995018137)
          ·
            refine ⟨84381558446294873246263603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112508744595059830995018137 84381558446294873246263603)
            ·
              refine ⟨126572337669442309869395405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84381558446294873246263603 126572337669442309869395405)
              ·
                refine ⟨47464626626040866201023277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126572337669442309869395405 47464626626040866201023277)
                ·
                  refine ⟨17799234984765324825383729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47464626626040866201023277 17799234984765324825383729)
                  ·
                    refine ⟨13349426238573993619037797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17799234984765324825383729 13349426238573993619037797)
                    ·
                      refine ⟨2503017419732623803569587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13349426238573993619037797 2503017419732623803569587)
                      ·
                        rfl

theorem cell23_4874609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_4874609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874609 prefixEnd_4874609 := by exact prefixLift 4874609
  have htrace : WordTrace (prefixWord ++ tailWord_4874609) baseStart_4874609 baseEnd_4874609 := by
    simpa [prefixWord, tailWord_4874609, baseEnd_4874609] using wordTrace_append hprefix tailTrace_4874609
  have hstable : (prefixWord ++ tailWord_4874609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874609).length < 2 ^ (prefixWord ++ tailWord_4874609).sum := by decide
  have hdescent : baseEnd_4874609 < baseStart_4874609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874613 : List Nat := [1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_4874613 : Nat := 118140960795 + 4874613 * 2 ^ 59
def prefixEnd_4874613 : Nat := 4983230072969 + 3 ^ 40 * 4874613 * 2
def baseEnd_4874613 : Nat := 2503019473655241787919569

theorem tailTrace_4874613 : CollatzResearch.WordTrace tailWord_4874613 prefixEnd_4874613 2503019473655241787919569 := by
  unfold tailWord_4874613
  simp only [CollatzResearch.WordTrace]
  refine ⟨177791742289117093465396493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118527828192744728976930995 177791742289117093465396493)
  ·
    refine ⟨66671903358418910049523685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177791742289117093465396493 66671903358418910049523685)
    ·
      refine ⟨12500981879703545634285691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66671903358418910049523685 12500981879703545634285691)
      ·
        refine ⟨18751472819555318451428537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12500981879703545634285691 18751472819555318451428537)
        ·
          refine ⟨14063604614666488838571403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18751472819555318451428537 14063604614666488838571403)
          ·
            refine ⟨21095406921999733257857105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14063604614666488838571403 21095406921999733257857105)
            ·
              refine ⟨15821555191499799943392829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21095406921999733257857105 15821555191499799943392829)
              ·
                refine ⟨5933083196812424978772311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15821555191499799943392829 5933083196812424978772311)
                ·
                  refine ⟨8899624795218637468158467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5933083196812424978772311 8899624795218637468158467)
                  ·
                    refine ⟨13349437192827956202237701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8899624795218637468158467 13349437192827956202237701)
                    ·
                      refine ⟨2503019473655241787919569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13349437192827956202237701 2503019473655241787919569)
                      ·
                        rfl

theorem cell23_4874613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_4874613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874613 prefixEnd_4874613 := by exact prefixLift 4874613
  have htrace : WordTrace (prefixWord ++ tailWord_4874613) baseStart_4874613 baseEnd_4874613 := by
    simpa [prefixWord, tailWord_4874613, baseEnd_4874613] using wordTrace_append hprefix tailTrace_4874613
  have hstable : (prefixWord ++ tailWord_4874613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874613).length < 2 ^ (prefixWord ++ tailWord_4874613).sum := by decide
  have hdescent : baseEnd_4874613 < baseStart_4874613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874619 : List Nat := [1, 1, 1, 1, 1, 9, 9]
def baseStart_4874619 : Nat := 118140960795 + 4874619 * 2 ^ 59
def prefixEnd_4874619 : Nat := 4983230072969 + 3 ^ 40 * 4874619 * 2
def baseEnd_4874619 : Nat := 30901513019002083511661

theorem tailTrace_4874619 : CollatzResearch.WordTrace tailWord_4874619 prefixEnd_4874619 30901513019002083511661 := by
  unfold tailWord_4874619
  simp only [CollatzResearch.WordTrace]
  refine ⟨177791961127095356490114911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118527974084730237660076607 177791961127095356490114911)
  ·
    refine ⟨266687941690643034735172367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177791961127095356490114911 266687941690643034735172367)
    ·
      refine ⟨400031912535964552102758551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266687941690643034735172367 400031912535964552102758551)
      ·
        refine ⟨600047868803946828154137827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400031912535964552102758551 600047868803946828154137827)
        ·
          refine ⟨900071803205920242231206741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600047868803946828154137827 900071803205920242231206741)
          ·
            refine ⟨5273858221909688919323477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 900071803205920242231206741 5273858221909688919323477)
            ·
              refine ⟨30901513019002083511661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5273858221909688919323477 30901513019002083511661)
              ·
                rfl

theorem cell23_4874619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 9].length) (baseStart_4874619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874619 prefixEnd_4874619 := by exact prefixLift 4874619
  have htrace : WordTrace (prefixWord ++ tailWord_4874619) baseStart_4874619 baseEnd_4874619 := by
    simpa [prefixWord, tailWord_4874619, baseEnd_4874619] using wordTrace_append hprefix tailTrace_4874619
  have hstable : (prefixWord ++ tailWord_4874619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874619).length < 2 ^ (prefixWord ++ tailWord_4874619).sum := by decide
  have hdescent : baseEnd_4874619 < baseStart_4874619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874650 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_4874650 : Nat := 118140960795 + 4874650 * 2 ^ 59
def prefixEnd_4874650 : Nat := 4983230072969 + 3 ^ 40 * 4874650 * 2
def baseEnd_4874650 : Nat := 2503038472439458143156899

theorem tailTrace_4874650 : CollatzResearch.WordTrace tailWord_4874650 prefixEnd_4874650 2503038472439458143156899 := by
  unfold tailWord_4874650
  simp only [CollatzResearch.WordTrace]
  refine ⟨44448272947495762196123351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118528727859988699189662269 44448272947495762196123351)
  ·
    refine ⟨66672409421243643294185027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44448272947495762196123351 66672409421243643294185027)
    ·
      refine ⟨100008614131865464941277541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66672409421243643294185027 100008614131865464941277541)
      ·
        refine ⟨18751615149724774676489539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100008614131865464941277541 18751615149724774676489539)
        ·
          refine ⟨28127422724587162014734309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18751615149724774676489539 28127422724587162014734309)
          ·
            refine ⟨5273891760860092877762683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28127422724587162014734309 5273891760860092877762683)
            ·
              refine ⟨7910837641290139316644025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5273891760860092877762683 7910837641290139316644025)
              ·
                refine ⟨5933128230967604487483019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7910837641290139316644025 5933128230967604487483019)
                ·
                  refine ⟨8899692346451406731224529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5933128230967604487483019 8899692346451406731224529)
                  ·
                    refine ⟨6674769259838555048418397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8899692346451406731224529 6674769259838555048418397)
                    ·
                      refine ⟨2503038472439458143156899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674769259838555048418397 2503038472439458143156899)
                      ·
                        rfl

theorem cell23_4874650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_4874650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874650 prefixEnd_4874650 := by exact prefixLift 4874650
  have htrace : WordTrace (prefixWord ++ tailWord_4874650) baseStart_4874650 baseEnd_4874650 := by
    simpa [prefixWord, tailWord_4874650, baseEnd_4874650] using wordTrace_append hprefix tailTrace_4874650
  have hstable : (prefixWord ++ tailWord_4874650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874650).length < 2 ^ (prefixWord ++ tailWord_4874650).sum := by decide
  have hdescent : baseEnd_4874650 < baseStart_4874650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874663 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3]
def baseStart_4874663 : Nat := 118140960795 + 4874663 * 2 ^ 59
def prefixEnd_4874663 : Nat := 4983230072969 + 3 ^ 40 * 4874663 * 2
def baseEnd_4874663 : Nat := 2503045147687966592294339

theorem tailTrace_4874663 : CollatzResearch.WordTrace tailWord_4874663 prefixEnd_4874663 2503045147687966592294339 := by
  unfold tailWord_4874663
  simp only [CollatzResearch.WordTrace]
  refine ⟨177793565938935952004716643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118529043959290634669811095 177793565938935952004716643)
  ·
    refine ⟨266690348908403928007074965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177793565938935952004716643 266690348908403928007074965)
    ·
      refine ⟨12501110105081434125331639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 266690348908403928007074965 12501110105081434125331639)
      ·
        refine ⟨18751665157622151187997459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12501110105081434125331639 18751665157622151187997459)
        ·
          refine ⟨28127497736433226781996189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18751665157622151187997459 28127497736433226781996189)
          ·
            refine ⟨10547811651162460043248571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28127497736433226781996189 10547811651162460043248571)
            ·
              refine ⟨15821717476743690064872857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10547811651162460043248571 15821717476743690064872857)
              ·
                refine ⟨11866288107557767548654643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15821717476743690064872857 11866288107557767548654643)
                ·
                  refine ⟨17799432161336651322981965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11866288107557767548654643 17799432161336651322981965)
                  ·
                    refine ⟨6674787060501244246118237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17799432161336651322981965 6674787060501244246118237)
                    ·
                      refine ⟨2503045147687966592294339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674787060501244246118237 2503045147687966592294339)
                      ·
                        rfl

theorem cell23_4874663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_4874663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874663 prefixEnd_4874663 := by exact prefixLift 4874663
  have htrace : WordTrace (prefixWord ++ tailWord_4874663) baseStart_4874663 baseEnd_4874663 := by
    simpa [prefixWord, tailWord_4874663, baseEnd_4874663] using wordTrace_append hprefix tailTrace_4874663
  have hstable : (prefixWord ++ tailWord_4874663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874663).length < 2 ^ (prefixWord ++ tailWord_4874663).sum := by decide
  have hdescent : baseEnd_4874663 < baseStart_4874663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874686 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_4874686 : Nat := 118140960795 + 4874686 * 2 ^ 59
def prefixEnd_4874686 : Nat := 4983230072969 + 3 ^ 40 * 4874686 * 2
def baseEnd_4874686 : Nat := 2503056957743020002306733

theorem tailTrace_4874686 : CollatzResearch.WordTrace tailWord_4874686 prefixEnd_4874686 2503056957743020002306733 := by
  unfold tailWord_4874686
  simp only [CollatzResearch.WordTrace]
  refine ⟨22224300602231578366600489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118529603211901751288535941 22224300602231578366600489)
  ·
    refine ⟨16668225451673683774950367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22224300602231578366600489 16668225451673683774950367)
    ·
      refine ⟨25002338177510525662425551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16668225451673683774950367 25002338177510525662425551)
      ·
        refine ⟨37503507266265788493638327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25002338177510525662425551 37503507266265788493638327)
        ·
          refine ⟨56255260899398682740457491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37503507266265788493638327 56255260899398682740457491)
          ·
            refine ⟨84382891349098024110686237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56255260899398682740457491 84382891349098024110686237)
            ·
              refine ⟨31643584255911759041507339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84382891349098024110686237 31643584255911759041507339)
              ·
                refine ⟨47465376383867638562261009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31643584255911759041507339 47465376383867638562261009)
                ·
                  refine ⟨35599032287900728921695757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47465376383867638562261009 35599032287900728921695757)
                  ·
                    refine ⟨13349637107962773345635909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35599032287900728921695757 13349637107962773345635909)
                    ·
                      refine ⟨2503056957743020002306733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13349637107962773345635909 2503056957743020002306733)
                      ·
                        rfl

theorem cell23_4874686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_4874686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874686 prefixEnd_4874686 := by exact prefixLift 4874686
  have htrace : WordTrace (prefixWord ++ tailWord_4874686) baseStart_4874686 baseEnd_4874686 := by
    simpa [prefixWord, tailWord_4874686, baseEnd_4874686] using wordTrace_append hprefix tailTrace_4874686
  have hstable : (prefixWord ++ tailWord_4874686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874686).length < 2 ^ (prefixWord ++ tailWord_4874686).sum := by decide
  have hdescent : baseEnd_4874686 < baseStart_4874686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874696 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 2, 6]
def baseStart_4874696 : Nat := 118140960795 + 4874696 * 2 ^ 59
def prefixEnd_4874696 : Nat := 4983230072969 + 3 ^ 40 * 4874696 * 2
def baseEnd_4874696 : Nat := 834354030849854987727229

theorem tailTrace_4874696 : CollatzResearch.WordTrace tailWord_4874696 prefixEnd_4874696 834354030849854987727229 := by
  unfold tailWord_4874696
  simp only [CollatzResearch.WordTrace]
  refine ⟨88897384773908199320333971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118529846365210932427111961 88897384773908199320333971)
  ·
    refine ⟨133346077160862298980500957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88897384773908199320333971 133346077160862298980500957)
    ·
      refine ⟨50004778935323362117687859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133346077160862298980500957 50004778935323362117687859)
      ·
        refine ⟨75007168402985043176531789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50004778935323362117687859 75007168402985043176531789)
        ·
          refine ⟨28127688151119391191199421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75007168402985043176531789 28127688151119391191199421)
          ·
            refine ⟨10547883056669771696699783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28127688151119391191199421 10547883056669771696699783)
            ·
              refine ⟨15821824585004657545049675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10547883056669771696699783 15821824585004657545049675)
              ·
                refine ⟨23732736877506986317574513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15821824585004657545049675 23732736877506986317574513)
                ·
                  refine ⟨17799552658130239738180885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23732736877506986317574513 17799552658130239738180885)
                  ·
                    refine ⟨834354030849854987727229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17799552658130239738180885 834354030849854987727229)
                    ·
                      rfl

theorem cell23_4874696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_4874696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874696 prefixEnd_4874696 := by exact prefixLift 4874696
  have htrace : WordTrace (prefixWord ++ tailWord_4874696) baseStart_4874696 baseEnd_4874696 := by
    simpa [prefixWord, tailWord_4874696, baseEnd_4874696] using wordTrace_append hprefix tailTrace_4874696
  have hstable : (prefixWord ++ tailWord_4874696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874696).length < 2 ^ (prefixWord ++ tailWord_4874696).sum := by decide
  have hdescent : baseEnd_4874696 < baseStart_4874696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874703 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 6, 2, 2]
def baseStart_4874703 : Nat := 118140960795 + 4874703 * 2 ^ 59
def prefixEnd_4874703 : Nat := 4983230072969 + 3 ^ 40 * 4874703 * 2
def baseEnd_4874703 : Nat := 2503065686914146435794155

theorem tailTrace_4874703 : CollatzResearch.WordTrace tailWord_4874703 prefixEnd_4874703 2503065686914146435794155 := by
  unfold tailWord_4874703
  simp only [CollatzResearch.WordTrace]
  refine ⟨177795024858791038836172763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118530016572527359224115175 177795024858791038836172763)
  ·
    refine ⟨266692537288186558254259145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177795024858791038836172763 266692537288186558254259145)
    ·
      refine ⟨200019402966139918690694359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266692537288186558254259145 200019402966139918690694359)
      ·
        refine ⟨300029104449209878036041539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200019402966139918690694359 300029104449209878036041539)
        ·
          refine ⟨450043656673814817054062309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300029104449209878036041539 450043656673814817054062309)
          ·
            refine ⟨84383185626340278197636683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 450043656673814817054062309 84383185626340278197636683)
            ·
              refine ⟨126574778439510417296455025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84383185626340278197636683 126574778439510417296455025)
              ·
                refine ⟨94931083829632812972341269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126574778439510417296455025 94931083829632812972341269)
                ·
                  refine ⟨4449894554514038108078497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94931083829632812972341269 4449894554514038108078497)
                  ·
                    refine ⟨3337420915885528581058873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4449894554514038108078497 3337420915885528581058873)
                    ·
                      refine ⟨2503065686914146435794155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337420915885528581058873 2503065686914146435794155)
                      ·
                        rfl

theorem cell23_4874703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 6, 2, 2].length) (baseStart_4874703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874703 prefixEnd_4874703 := by exact prefixLift 4874703
  have htrace : WordTrace (prefixWord ++ tailWord_4874703) baseStart_4874703 baseEnd_4874703 := by
    simpa [prefixWord, tailWord_4874703, baseEnd_4874703] using wordTrace_append hprefix tailTrace_4874703
  have hstable : (prefixWord ++ tailWord_4874703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874703).length < 2 ^ (prefixWord ++ tailWord_4874703).sum := by decide
  have hdescent : baseEnd_4874703 < baseStart_4874703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874733 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_4874733 : Nat := 118140960795 + 4874733 * 2 ^ 59
def prefixEnd_4874733 : Nat := 4983230072969 + 3 ^ 40 * 4874733 * 2
def baseEnd_4874733 : Nat := 2503081091333781318419017

theorem tailTrace_4874733 : CollatzResearch.WordTrace tailWord_4874733 prefixEnd_4874733 2503081091333781318419017 := by
  unfold tailWord_4874733
  simp only [CollatzResearch.WordTrace]
  refine ⟨177796119048682353959764853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118530746032454902639843235 177796119048682353959764853)
  ·
    refine ⟨16668386160813970683727955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177796119048682353959764853 16668386160813970683727955)
    ·
      refine ⟨25002579241220956025591933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16668386160813970683727955 25002579241220956025591933)
      ·
        refine ⟨9375967215457858509596975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25002579241220956025591933 9375967215457858509596975)
        ·
          refine ⟨14063950823186787764395463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9375967215457858509596975 14063950823186787764395463)
          ·
            refine ⟨21095926234780181646593195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14063950823186787764395463 21095926234780181646593195)
            ·
              refine ⟨31643889352170272469889793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21095926234780181646593195 31643889352170272469889793)
              ·
                refine ⟨23732917014127704352417345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31643889352170272469889793 23732917014127704352417345)
                ·
                  refine ⟨17799687760595778264313009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23732917014127704352417345 17799687760595778264313009)
                  ·
                    refine ⟨13349765820446833698234757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17799687760595778264313009 13349765820446833698234757)
                    ·
                      refine ⟨2503081091333781318419017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13349765820446833698234757 2503081091333781318419017)
                      ·
                        rfl

theorem cell23_4874733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_4874733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874733 prefixEnd_4874733 := by exact prefixLift 4874733
  have htrace : WordTrace (prefixWord ++ tailWord_4874733) baseStart_4874733 baseEnd_4874733 := by
    simpa [prefixWord, tailWord_4874733, baseEnd_4874733] using wordTrace_append hprefix tailTrace_4874733
  have hstable : (prefixWord ++ tailWord_4874733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874733).length < 2 ^ (prefixWord ++ tailWord_4874733).sum := by decide
  have hdescent : baseEnd_4874733 < baseStart_4874733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874736 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3]
def baseStart_4874736 : Nat := 118140960795 + 4874736 * 2 ^ 59
def prefixEnd_4874736 : Nat := 4983230072969 + 3 ^ 40 * 4874736 * 2
def baseEnd_4874736 : Nat := 2503082631775744806681503

theorem tailTrace_4874736 : CollatzResearch.WordTrace tailWord_4874736 prefixEnd_4874736 2503082631775744806681503 := by
  unfold tailWord_4874736
  simp only [CollatzResearch.WordTrace]
  refine ⟨88898114233835742736062031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118530818978447656981416041 88898114233835742736062031)
  ·
    refine ⟨133347171350753614104093047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88898114233835742736062031 133347171350753614104093047)
    ·
      refine ⟨200020757026130421156139571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133347171350753614104093047 200020757026130421156139571)
      ·
        refine ⟨300031135539195631734209357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200020757026130421156139571 300031135539195631734209357)
        ·
          refine ⟨112511675827198361900328509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300031135539195631734209357 112511675827198361900328509)
          ·
            refine ⟨42191878435199385712623191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112511675827198361900328509 42191878435199385712623191)
            ·
              refine ⟨63287817652799078568934787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42191878435199385712623191 63287817652799078568934787)
              ·
                refine ⟨94931726479198617853402181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63287817652799078568934787 94931726479198617853402181)
                ·
                  refine ⟨17799698714849740847512909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94931726479198617853402181 17799698714849740847512909)
                  ·
                    refine ⟨6674887018068652817817341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17799698714849740847512909 6674887018068652817817341)
                    ·
                      refine ⟨2503082631775744806681503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674887018068652817817341 2503082631775744806681503)
                      ·
                        rfl

theorem cell23_4874736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 3].length) (baseStart_4874736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874736 prefixEnd_4874736 := by exact prefixLift 4874736
  have htrace : WordTrace (prefixWord ++ tailWord_4874736) baseStart_4874736 baseEnd_4874736 := by
    simpa [prefixWord, tailWord_4874736, baseEnd_4874736] using wordTrace_append hprefix tailTrace_4874736
  have hstable : (prefixWord ++ tailWord_4874736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874736).length < 2 ^ (prefixWord ++ tailWord_4874736).sum := by decide
  have hdescent : baseEnd_4874736 < baseStart_4874736 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874753 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4874753 : Nat := 118140960795 + 4874753 * 2 ^ 59
def prefixEnd_4874753 : Nat := 4983230072969 + 3 ^ 40 * 4874753 * 2
def baseEnd_4874753 : Nat := 2503091360946871240168925

theorem tailTrace_4874753 : CollatzResearch.WordTrace tailWord_4874753 prefixEnd_4874753 2503091360946871240168925 := by
  unfold tailWord_4874753
  simp only [CollatzResearch.WordTrace]
  refine ⟨177796848508609897375492913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118531232339073264916995275 177796848508609897375492913)
  ·
    refine ⟨133347636381457423031619685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177796848508609897375492913 133347636381457423031619685)
    ·
      refine ⟨25002681821523266818428691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133347636381457423031619685 25002681821523266818428691)
      ·
        refine ⟨37504022732284900227643037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25002681821523266818428691 37504022732284900227643037)
        ·
          refine ⟨14064008524606837585366139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37504022732284900227643037 14064008524606837585366139)
          ·
            refine ⟨21096012786910256378049209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14064008524606837585366139 21096012786910256378049209)
            ·
              refine ⟨15822009590182692283536907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21096012786910256378049209 15822009590182692283536907)
              ·
                refine ⟨23733014385274038425305361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15822009590182692283536907 23733014385274038425305361)
                ·
                  refine ⟨17799760788955528818979021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23733014385274038425305361 17799760788955528818979021)
                  ·
                    refine ⟨6674910295858323307117133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17799760788955528818979021 6674910295858323307117133)
                    ·
                      refine ⟨2503091360946871240168925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6674910295858323307117133 2503091360946871240168925)
                      ·
                        rfl

theorem cell23_4874753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4874753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874753 prefixEnd_4874753 := by exact prefixLift 4874753
  have htrace : WordTrace (prefixWord ++ tailWord_4874753) baseStart_4874753 baseEnd_4874753 := by
    simpa [prefixWord, tailWord_4874753, baseEnd_4874753] using wordTrace_append hprefix tailTrace_4874753
  have hstable : (prefixWord ++ tailWord_4874753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874753).length < 2 ^ (prefixWord ++ tailWord_4874753).sum := by decide
  have hdescent : baseEnd_4874753 < baseStart_4874753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874754 : List Nat := [3, 4, 1, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_4874754 : Nat := 118140960795 + 4874754 * 2 ^ 59
def prefixEnd_4874754 : Nat := 4983230072969 + 3 ^ 40 * 4874754 * 2
def baseEnd_4874754 : Nat := 2503091874427525736256421

theorem tailTrace_4874754 : CollatzResearch.WordTrace tailWord_4874754 prefixEnd_4874754 2503091874427525736256421 := by
  unfold tailWord_4874754
  simp only [CollatzResearch.WordTrace]
  refine ⟨44449221245401568636569829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118531256654404183030852877 44449221245401568636569829)
  ·
    refine ⟨8334228983512794119356843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44449221245401568636569829 8334228983512794119356843)
    ·
      refine ⟨12501343475269191179035265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334228983512794119356843 12501343475269191179035265)
      ·
        refine ⟨9376007606451893384276449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12501343475269191179035265 9376007606451893384276449)
        ·
          refine ⟨7032005704838920038207337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9376007606451893384276449 7032005704838920038207337)
          ·
            refine ⟨5274004278629190028655503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7032005704838920038207337 5274004278629190028655503)
            ·
              refine ⟨7911006417943785042983255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274004278629190028655503 7911006417943785042983255)
              ·
                refine ⟨11866509626915677564474883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7911006417943785042983255 11866509626915677564474883)
                ·
                  refine ⟨17799764440373516346712325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11866509626915677564474883 17799764440373516346712325)
                  ·
                    refine ⟨3337455832570034315008561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17799764440373516346712325 3337455832570034315008561)
                    ·
                      refine ⟨2503091874427525736256421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337455832570034315008561 2503091874427525736256421)
                      ·
                        rfl

theorem cell23_4874754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_4874754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874754 prefixEnd_4874754 := by exact prefixLift 4874754
  have htrace : WordTrace (prefixWord ++ tailWord_4874754) baseStart_4874754 baseEnd_4874754 := by
    simpa [prefixWord, tailWord_4874754, baseEnd_4874754] using wordTrace_append hprefix tailTrace_4874754
  have hstable : (prefixWord ++ tailWord_4874754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874754).length < 2 ^ (prefixWord ++ tailWord_4874754).sum := by decide
  have hdescent : baseEnd_4874754 < baseStart_4874754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874877 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 3]
def baseStart_4874877 : Nat := 118140960795 + 4874877 * 2 ^ 59
def prefixEnd_4874877 : Nat := 4983230072969 + 3 ^ 40 * 4874877 * 2
def baseEnd_4874877 : Nat := 2503155032548028755018355

theorem tailTrace_4874877 : CollatzResearch.WordTrace tailWord_4874877 prefixEnd_4874877 2503155032548028755018355 := by
  unfold tailWord_4874877
  simp only [CollatzResearch.WordTrace]
  refine ⟨177801371160160666553006885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118534247440107111035337923 177801371160160666553006885)
  ·
    refine ⟨33337757092530124978688791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177801371160160666553006885 33337757092530124978688791)
    ·
      refine ⟨50006635638795187468033187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33337757092530124978688791 50006635638795187468033187)
      ·
        refine ⟨75009953458192781202049781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50006635638795187468033187 75009953458192781202049781)
        ·
          refine ⟨7032183136705573237692167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75009953458192781202049781 7032183136705573237692167)
          ·
            refine ⟨10548274705058359856538251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7032183136705573237692167 10548274705058359856538251)
            ·
              refine ⟨15822412057587539784807377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10548274705058359856538251 15822412057587539784807377)
              ·
                refine ⟨11866809043190654838605533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15822412057587539784807377 11866809043190654838605533)
                ·
                  refine ⟨4450053391196495564477075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11866809043190654838605533 4450053391196495564477075)
                  ·
                    refine ⟨6675080086794743346715613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450053391196495564477075 6675080086794743346715613)
                    ·
                      refine ⟨2503155032548028755018355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675080086794743346715613 2503155032548028755018355)
                      ·
                        rfl

theorem cell23_4874877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_4874877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874877 prefixEnd_4874877 := by exact prefixLift 4874877
  have htrace : WordTrace (prefixWord ++ tailWord_4874877) baseStart_4874877 baseEnd_4874877 := by
    simpa [prefixWord, tailWord_4874877, baseEnd_4874877] using wordTrace_append hprefix tailTrace_4874877
  have hstable : (prefixWord ++ tailWord_4874877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874877).length < 2 ^ (prefixWord ++ tailWord_4874877).sum := by decide
  have hdescent : baseEnd_4874877 < baseStart_4874877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874883 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4]
def baseStart_4874883 : Nat := 118140960795 + 4874883 * 2 ^ 59
def prefixEnd_4874883 : Nat := 4983230072969 + 3 ^ 40 * 4874883 * 2
def baseEnd_4874883 : Nat := 2503158113431955731543327

theorem tailTrace_4874883 : CollatzResearch.WordTrace tailWord_4874883 prefixEnd_4874883 2503158113431955731543327 := by
  unfold tailWord_4874883
  simp only [CollatzResearch.WordTrace]
  refine ⟨177801589998138929577725303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118534393332092619718483535 177801589998138929577725303)
  ·
    refine ⟨266702384997208394366587955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177801589998138929577725303 266702384997208394366587955)
    ·
      refine ⟨400053577495812591549881933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266702384997208394366587955 400053577495812591549881933)
      ·
        refine ⟨150020091560929721831205725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400053577495812591549881933 150020091560929721831205725)
        ·
          refine ⟨56257534335348645686702147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150020091560929721831205725 56257534335348645686702147)
          ·
            refine ⟨84386301503022968530053221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56257534335348645686702147 84386301503022968530053221)
            ·
              refine ⟨15822431531816806599384979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84386301503022968530053221 15822431531816806599384979)
              ·
                refine ⟨23733647297725209899077469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15822431531816806599384979 23733647297725209899077469)
                ·
                  refine ⟨8900117736646953712154051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23733647297725209899077469 8900117736646953712154051)
                  ·
                    refine ⟨13350176604970430568231077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8900117736646953712154051 13350176604970430568231077)
                    ·
                      refine ⟨2503158113431955731543327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13350176604970430568231077 2503158113431955731543327)
                      ·
                        rfl

theorem cell23_4874883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_4874883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874883 prefixEnd_4874883 := by exact prefixLift 4874883
  have htrace : WordTrace (prefixWord ++ tailWord_4874883) baseStart_4874883 baseEnd_4874883 := by
    simpa [prefixWord, tailWord_4874883, baseEnd_4874883] using wordTrace_append hprefix tailTrace_4874883
  have hstable : (prefixWord ++ tailWord_4874883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874883).length < 2 ^ (prefixWord ++ tailWord_4874883).sum := by decide
  have hdescent : baseEnd_4874883 < baseStart_4874883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874894 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3]
def baseStart_4874894 : Nat := 118140960795 + 4874894 * 2 ^ 59
def prefixEnd_4874894 : Nat := 4983230072969 + 3 ^ 40 * 4874894 * 2
def baseEnd_4874894 : Nat := 2503163761719155188505777

theorem tailTrace_4874894 : CollatzResearch.WordTrace tailWord_4874894 prefixEnd_4874894 2503163761719155188505777 := by
  unfold tailWord_4874894
  simp only [CollatzResearch.WordTrace]
  refine ⟨22225248900137384807046967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118534660800732718970917157 22225248900137384807046967)
  ·
    refine ⟨33337873350206077210570451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22225248900137384807046967 33337873350206077210570451)
    ·
      refine ⟨50006810025309115815855677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33337873350206077210570451 50006810025309115815855677)
      ·
        refine ⟨18752553759490918430945879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50006810025309115815855677 18752553759490918430945879)
        ·
          refine ⟨28128830639236377646418819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18752553759490918430945879 28128830639236377646418819)
          ·
            refine ⟨42193245958854566469628229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28128830639236377646418819 42193245958854566469628229)
            ·
              refine ⟨7911233617285231213055293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42193245958854566469628229 7911233617285231213055293)
              ·
                refine ⟨2966712606481961704895735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7911233617285231213055293 2966712606481961704895735)
                ·
                  refine ⟨4450068909722942557343603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966712606481961704895735 4450068909722942557343603)
                  ·
                    refine ⟨6675103364584413836015405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450068909722942557343603 6675103364584413836015405)
                    ·
                      refine ⟨2503163761719155188505777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675103364584413836015405 2503163761719155188505777)
                      ·
                        rfl

theorem cell23_4874894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_4874894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874894 prefixEnd_4874894 := by exact prefixLift 4874894
  have htrace : WordTrace (prefixWord ++ tailWord_4874894) baseStart_4874894 baseEnd_4874894 := by
    simpa [prefixWord, tailWord_4874894, baseEnd_4874894] using wordTrace_append hprefix tailTrace_4874894
  have hstable : (prefixWord ++ tailWord_4874894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874894).length < 2 ^ (prefixWord ++ tailWord_4874894).sum := by decide
  have hdescent : baseEnd_4874894 < baseStart_4874894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874896 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_4874896 : Nat := 118140960795 + 4874896 * 2 ^ 59
def prefixEnd_4874896 : Nat := 4983230072969 + 3 ^ 40 * 4874896 * 2
def baseEnd_4874896 : Nat := 2503164788680464180680767

theorem tailTrace_4874896 : CollatzResearch.WordTrace tailWord_4874896 prefixEnd_4874896 2503164788680464180680767 := by
  unfold tailWord_4874896
  simp only [CollatzResearch.WordTrace]
  refine ⟨88901032073545916398974271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118534709431394555198632361 88901032073545916398974271)
  ·
    refine ⟨133351548110318874598461407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88901032073545916398974271 133351548110318874598461407)
    ·
      refine ⟨200027322165478311897692111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133351548110318874598461407 200027322165478311897692111)
      ·
        refine ⟨300040983248217467846538167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200027322165478311897692111 300040983248217467846538167)
        ·
          refine ⟨450061474872326201769807251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300040983248217467846538167 450061474872326201769807251)
          ·
            refine ⟨675092212308489302654710877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450061474872326201769807251 675092212308489302654710877)
            ·
              refine ⟨253159579615683488495516579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675092212308489302654710877 253159579615683488495516579)
              ·
                refine ⟨379739369423525232743274869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253159579615683488495516579 379739369423525232743274869)
                ·
                  refine ⟨35600565883455490569682019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 379739369423525232743274869 35600565883455490569682019)
                  ·
                    refine ⟨53400848825183235854523029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35600565883455490569682019 53400848825183235854523029)
                    ·
                      refine ⟨2503164788680464180680767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53400848825183235854523029 2503164788680464180680767)
                      ·
                        rfl

theorem cell23_4874896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_4874896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874896 prefixEnd_4874896 := by exact prefixLift 4874896
  have htrace : WordTrace (prefixWord ++ tailWord_4874896) baseStart_4874896 baseEnd_4874896 := by
    simpa [prefixWord, tailWord_4874896, baseEnd_4874896] using wordTrace_append hprefix tailTrace_4874896
  have hstable : (prefixWord ++ tailWord_4874896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874896).length < 2 ^ (prefixWord ++ tailWord_4874896).sum := by decide
  have hdescent : baseEnd_4874896 < baseStart_4874896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874903 : List Nat := [1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_4874903 : Nat := 118140960795 + 4874903 * 2 ^ 59
def prefixEnd_4874903 : Nat := 4983230072969 + 3 ^ 40 * 4874903 * 2
def baseEnd_4874903 : Nat := 2503168383045045653293235

theorem tailTrace_4874903 : CollatzResearch.WordTrace tailWord_4874903 prefixEnd_4874903 2503168383045045653293235 := by
  unfold tailWord_4874903
  simp only [CollatzResearch.WordTrace]
  refine ⟨177802319458066472993453363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118534879638710981995635575 177802319458066472993453363)
  ·
    refine ⟨266703479187099709490180045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177802319458066472993453363 266703479187099709490180045)
    ·
      refine ⟨100013804695162391058817517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266703479187099709490180045 100013804695162391058817517)
      ·
        refine ⟨37505176760685896647056569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100013804695162391058817517 37505176760685896647056569)
        ·
          refine ⟨28128882570514422485292427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37505176760685896647056569 28128882570514422485292427)
          ·
            refine ⟨42193323855771633727938641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28128882570514422485292427 42193323855771633727938641)
            ·
              refine ⟨31644992891828725295953981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42193323855771633727938641 31644992891828725295953981)
              ·
                refine ⟨11866872334435771985982743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31644992891828725295953981 11866872334435771985982743)
                ·
                  refine ⟨17800308501653657978974115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11866872334435771985982743 17800308501653657978974115)
                  ·
                    refine ⟨26700462752480486968461173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17800308501653657978974115 26700462752480486968461173)
                    ·
                      refine ⟨2503168383045045653293235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26700462752480486968461173 2503168383045045653293235)
                      ·
                        rfl

theorem cell23_4874903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_4874903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874903 prefixEnd_4874903 := by exact prefixLift 4874903
  have htrace : WordTrace (prefixWord ++ tailWord_4874903) baseStart_4874903 baseEnd_4874903 := by
    simpa [prefixWord, tailWord_4874903, baseEnd_4874903] using wordTrace_append hprefix tailTrace_4874903
  have hstable : (prefixWord ++ tailWord_4874903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874903).length < 2 ^ (prefixWord ++ tailWord_4874903).sum := by decide
  have hdescent : baseEnd_4874903 < baseStart_4874903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874927 : List Nat := [1, 1, 2, 1, 2, 6, 3, 1, 2, 4]
def baseStart_4874927 : Nat := 118140960795 + 4874927 * 2 ^ 59
def prefixEnd_4874927 : Nat := 4983230072969 + 3 ^ 40 * 4874927 * 2
def baseEnd_4874927 : Nat := 834393568860251186464375

theorem tailTrace_4874927 : CollatzResearch.WordTrace tailWord_4874927 prefixEnd_4874927 834393568860251186464375 := by
  unfold tailWord_4874927
  simp only [CollatzResearch.WordTrace]
  refine ⟨177803194809979525092327035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118535463206653016728218023 177803194809979525092327035)
  ·
    refine ⟨266704792214969287638490553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177803194809979525092327035 266704792214969287638490553)
    ·
      refine ⟨200028594161226965728867915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266704792214969287638490553 200028594161226965728867915)
      ·
        refine ⟨300042891241840448593301873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200028594161226965728867915 300042891241840448593301873)
        ·
          refine ⟨225032168431380336444976405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300042891241840448593301873 225032168431380336444976405)
          ·
            refine ⟨10548382895220953270858269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 225032168431380336444976405 10548382895220953270858269)
            ·
              refine ⟨3955643585707857476571851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10548382895220953270858269 3955643585707857476571851)
              ·
                refine ⟨5933465378561786214857777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3955643585707857476571851 5933465378561786214857777)
                ·
                  refine ⟨4450099033921339661143333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5933465378561786214857777 4450099033921339661143333)
                  ·
                    refine ⟨834393568860251186464375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450099033921339661143333 834393568860251186464375)
                    ·
                      rfl

theorem cell23_4874927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_4874927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874927 prefixEnd_4874927 := by exact prefixLift 4874927
  have htrace : WordTrace (prefixWord ++ tailWord_4874927) baseStart_4874927 baseEnd_4874927 := by
    simpa [prefixWord, tailWord_4874927, baseEnd_4874927] using wordTrace_append hprefix tailTrace_4874927
  have hstable : (prefixWord ++ tailWord_4874927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874927).length < 2 ^ (prefixWord ++ tailWord_4874927).sum := by decide
  have hdescent : baseEnd_4874927 < baseStart_4874927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874945 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4874945 : Nat := 118140960795 + 4874945 * 2 ^ 59
def prefixEnd_4874945 : Nat := 4983230072969 + 3 ^ 40 * 4874945 * 2
def baseEnd_4874945 : Nat := 2503189949232534488968043

theorem tailTrace_4874945 : CollatzResearch.WordTrace tailWord_4874945 prefixEnd_4874945 2503189949232534488968043 := by
  unfold tailWord_4874945
  simp only [CollatzResearch.WordTrace]
  refine ⟨177803851323914314166482289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118535900882609542777654859 177803851323914314166482289)
  ·
    refine ⟨133352888492935735624861717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177803851323914314166482289 133352888492935735624861717)
    ·
      refine ⟨6250916648106362607415393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133352888492935735624861717 6250916648106362607415393)
      ·
        refine ⟨4688187486079771955561545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6250916648106362607415393 4688187486079771955561545)
        ·
          refine ⟨3516140614559828966671159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4688187486079771955561545 3516140614559828966671159)
          ·
            refine ⟨5274210921839743450006739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516140614559828966671159 5274210921839743450006739)
            ·
              refine ⟨7911316382759615175010109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274210921839743450006739 7911316382759615175010109)
              ·
                refine ⟨2966743643534855690628791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7911316382759615175010109 2966743643534855690628791)
                ·
                  refine ⟨4450115465302283535943187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966743643534855690628791 4450115465302283535943187)
                  ·
                    refine ⟨6675173197953425303914781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450115465302283535943187 6675173197953425303914781)
                    ·
                      refine ⟨2503189949232534488968043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675173197953425303914781 2503189949232534488968043)
                      ·
                        rfl

theorem cell23_4874945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4874945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874945 prefixEnd_4874945 := by exact prefixLift 4874945
  have htrace : WordTrace (prefixWord ++ tailWord_4874945) baseStart_4874945 baseEnd_4874945 := by
    simpa [prefixWord, tailWord_4874945, baseEnd_4874945] using wordTrace_append hprefix tailTrace_4874945
  have hstable : (prefixWord ++ tailWord_4874945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874945).length < 2 ^ (prefixWord ++ tailWord_4874945).sum := by decide
  have hdescent : baseEnd_4874945 < baseStart_4874945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874957 : List Nat := [1, 6, 2, 1, 2, 2, 9]
def baseStart_4874957 : Nat := 118140960795 + 4874957 * 2 ^ 59
def prefixEnd_4874957 : Nat := 4983230072969 + 3 ^ 40 * 4874957 * 2
def baseEnd_4874957 : Nat := 30903655691362820271827

theorem tailTrace_4874957 : CollatzResearch.WordTrace tailWord_4874957 prefixEnd_4874957 30903655691362820271827 := by
  unfold tailWord_4874957
  simp only [CollatzResearch.WordTrace]
  refine ⟨177804288999870840215919125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118536192666580560143946083 177804288999870840215919125)
  ·
    refine ⟨8334576046868945635121209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177804288999870840215919125 8334576046868945635121209)
    ·
      refine ⟨6250932035151709226340907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8334576046868945635121209 6250932035151709226340907)
      ·
        refine ⟨9376398052727563839511361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6250932035151709226340907 9376398052727563839511361)
        ·
          refine ⟨7032298539545672879633521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9376398052727563839511361 7032298539545672879633521)
          ·
            refine ⟨5274223904659254659725141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7032298539545672879633521 5274223904659254659725141)
            ·
              refine ⟨30903655691362820271827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5274223904659254659725141 30903655691362820271827)
              ·
                rfl

theorem cell23_4874957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 9].length) (baseStart_4874957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874957 prefixEnd_4874957 := by exact prefixLift 4874957
  have htrace : WordTrace (prefixWord ++ tailWord_4874957) baseStart_4874957 baseEnd_4874957 := by
    simpa [prefixWord, tailWord_4874957, baseEnd_4874957] using wordTrace_append hprefix tailTrace_4874957
  have hstable : (prefixWord ++ tailWord_4874957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874957).length < 2 ^ (prefixWord ++ tailWord_4874957).sum := by decide
  have hdescent : baseEnd_4874957 < baseStart_4874957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874984 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3]
def baseStart_4874984 : Nat := 118140960795 + 4874984 * 2 ^ 59
def prefixEnd_4874984 : Nat := 4983230072969 + 3 ^ 40 * 4874984 * 2
def baseEnd_4874984 : Nat := 2503209974978059836380363

theorem tailTrace_4874984 : CollatzResearch.WordTrace tailWord_4874984 prefixEnd_4874984 2503209974978059836380363 := by
  unfold tailWord_4874984
  simp only [CollatzResearch.WordTrace]
  refine ⟨88902636885386511913576003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118536849180515349218101337 88902636885386511913576003)
  ·
    refine ⟨133353955328079767870364005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88902636885386511913576003 133353955328079767870364005)
    ·
      refine ⟨25003866624014956475693251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133353955328079767870364005 25003866624014956475693251)
      ·
        refine ⟨37505799936022434713539877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25003866624014956475693251 37505799936022434713539877)
        ·
          refine ⟨7032337488004206508788727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37505799936022434713539877 7032337488004206508788727)
          ·
            refine ⟨10548506232006309763183091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7032337488004206508788727 10548506232006309763183091)
            ·
              refine ⟨15822759348009464644774637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10548506232006309763183091 15822759348009464644774637)
              ·
                refine ⟨5933534755503549241790489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15822759348009464644774637 5933534755503549241790489)
                ·
                  refine ⟨4450151066627661931342867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5933534755503549241790489 4450151066627661931342867)
                  ·
                    refine ⟨6675226599941492897014301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450151066627661931342867 6675226599941492897014301)
                    ·
                      refine ⟨2503209974978059836380363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675226599941492897014301 2503209974978059836380363)
                      ·
                        rfl

theorem cell23_4874984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_4874984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874984 prefixEnd_4874984 := by exact prefixLift 4874984
  have htrace : WordTrace (prefixWord ++ tailWord_4874984) baseStart_4874984 baseEnd_4874984 := by
    simpa [prefixWord, tailWord_4874984, baseEnd_4874984] using wordTrace_append hprefix tailTrace_4874984
  have hstable : (prefixWord ++ tailWord_4874984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874984).length < 2 ^ (prefixWord ++ tailWord_4874984).sum := by decide
  have hdescent : baseEnd_4874984 < baseStart_4874984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874993 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_4874993 : Nat := 118140960795 + 4874993 * 2 ^ 59
def prefixEnd_4874993 : Nat := 4983230072969 + 3 ^ 40 * 4874993 * 2
def baseEnd_4874993 : Nat := 2503214596303950301167821

theorem tailTrace_4874993 : CollatzResearch.WordTrace tailWord_4874993 prefixEnd_4874993 2503214596303950301167821 := by
  unfold tailWord_4874993
  simp only [CollatzResearch.WordTrace]
  refine ⟨177805602027740418364229633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118537068018493612242819755 177805602027740418364229633)
  ·
    refine ⟨133354201520805313773172225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177805602027740418364229633 133354201520805313773172225)
    ·
      refine ⟨100015651140603985329879169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133354201520805313773172225 100015651140603985329879169)
      ·
        refine ⟨75011738355452988997409377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100015651140603985329879169 75011738355452988997409377)
        ·
          refine ⟨56258803766589741748057033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75011738355452988997409377 56258803766589741748057033)
          ·
            refine ⟨42194102824942306311042775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56258803766589741748057033 42194102824942306311042775)
            ·
              refine ⟨63291154237413459466564163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42194102824942306311042775 63291154237413459466564163)
              ·
                refine ⟨94936731356120189199846245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63291154237413459466564163 94936731356120189199846245)
                ·
                  refine ⟨17800637129272535474971171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94936731356120189199846245 17800637129272535474971171)
                  ·
                    refine ⟨26700955693908803212456757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17800637129272535474971171 26700955693908803212456757)
                    ·
                      refine ⟨2503214596303950301167821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26700955693908803212456757 2503214596303950301167821)
                      ·
                        rfl

theorem cell23_4874993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_4874993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874993 prefixEnd_4874993 := by exact prefixLift 4874993
  have htrace : WordTrace (prefixWord ++ tailWord_4874993) baseStart_4874993 baseEnd_4874993 := by
    simpa [prefixWord, tailWord_4874993, baseEnd_4874993] using wordTrace_append hprefix tailTrace_4874993
  have hstable : (prefixWord ++ tailWord_4874993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874993).length < 2 ^ (prefixWord ++ tailWord_4874993).sum := by decide
  have hdescent : baseEnd_4874993 < baseStart_4874993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4874994 : List Nat := [3, 2, 1, 3, 1, 2, 3, 2, 1, 3, 2]
def baseStart_4874994 : Nat := 118140960795 + 4874994 * 2 ^ 59
def prefixEnd_4874994 : Nat := 4983230072969 + 3 ^ 40 * 4874994 * 2
def baseEnd_4874994 : Nat := 2503215109784604797255317

theorem tailTrace_4874994 : CollatzResearch.WordTrace tailWord_4874994 prefixEnd_4874994 2503215109784604797255317 := by
  unfold tailWord_4874994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44451409625184198883754009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118537092333824530356677357 44451409625184198883754009)
  ·
    refine ⟨33338557218888149162815507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44451409625184198883754009 33338557218888149162815507)
    ·
      refine ⟨50007835828332223744223261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33338557218888149162815507 50007835828332223744223261)
      ·
        refine ⟨18752938435624583904083723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50007835828332223744223261 18752938435624583904083723)
        ·
          refine ⟨28129407653436875856125585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18752938435624583904083723 28129407653436875856125585)
          ·
            refine ⟨21097055740077656892094189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28129407653436875856125585 21097055740077656892094189)
            ·
              refine ⟨7911395902529121334535321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21097055740077656892094189 7911395902529121334535321)
              ·
                refine ⟨5933546926896841000901491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7911395902529121334535321 5933546926896841000901491)
                ·
                  refine ⟨8900320390345261501352237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5933546926896841000901491 8900320390345261501352237)
                  ·
                    refine ⟨3337620146379473063007089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8900320390345261501352237 3337620146379473063007089)
                    ·
                      refine ⟨2503215109784604797255317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337620146379473063007089 2503215109784604797255317)
                      ·
                        rfl

theorem cell23_4874994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_4874994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4874994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4874994 prefixEnd_4874994 := by exact prefixLift 4874994
  have htrace : WordTrace (prefixWord ++ tailWord_4874994) baseStart_4874994 baseEnd_4874994 := by
    simpa [prefixWord, tailWord_4874994, baseEnd_4874994] using wordTrace_append hprefix tailTrace_4874994
  have hstable : (prefixWord ++ tailWord_4874994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4874994).length < 2 ^ (prefixWord ++ tailWord_4874994).sum := by decide
  have hdescent : baseEnd_4874994 < baseStart_4874994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4874994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875040 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3]
def baseStart_4875040 : Nat := 118140960795 + 4875040 * 2 ^ 59
def prefixEnd_4875040 : Nat := 4983230072969 + 3 ^ 40 * 4875040 * 2
def baseEnd_4875040 : Nat := 2503238729894711617280105

theorem tailTrace_4875040 : CollatzResearch.WordTrace tailWord_4875040 prefixEnd_4875040 2503238729894711617280105 := by
  unfold tailWord_4875040
  simp only [CollatzResearch.WordTrace]
  refine ⟨88903658129285072695595287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118538210839046763594127049 88903658129285072695595287)
  ·
    refine ⟨133355487193927609043392931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88903658129285072695595287 133355487193927609043392931)
    ·
      refine ⟨200033230790891413565089397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133355487193927609043392931 200033230790891413565089397)
      ·
        refine ⟨18753115386646070021727131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200033230790891413565089397 18753115386646070021727131)
        ·
          refine ⟨28129673079969105032590697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18753115386646070021727131 28129673079969105032590697)
          ·
            refine ⟨21097254809976828774443023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28129673079969105032590697 21097254809976828774443023)
            ·
              refine ⟨31645882214965243161664535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21097254809976828774443023 31645882214965243161664535)
              ·
                refine ⟨47468823322447864742496803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31645882214965243161664535 47468823322447864742496803)
                ·
                  refine ⟨71203234983671797113745205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47468823322447864742496803 71203234983671797113745205)
                  ·
                    refine ⟨6675303279719230979413613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71203234983671797113745205 6675303279719230979413613)
                    ·
                      refine ⟨2503238729894711617280105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675303279719230979413613 2503238729894711617280105)
                      ·
                        rfl

theorem cell23_4875040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_4875040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875040 prefixEnd_4875040 := by exact prefixLift 4875040
  have htrace : WordTrace (prefixWord ++ tailWord_4875040) baseStart_4875040 baseEnd_4875040 := by
    simpa [prefixWord, tailWord_4875040, baseEnd_4875040] using wordTrace_append hprefix tailTrace_4875040
  have hstable : (prefixWord ++ tailWord_4875040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875040).length < 2 ^ (prefixWord ++ tailWord_4875040).sum := by decide
  have hdescent : baseEnd_4875040 < baseStart_4875040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875043 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 1, 7]
def baseStart_4875043 : Nat := 118140960795 + 4875043 * 2 ^ 59
def prefixEnd_4875043 : Nat := 4983230072969 + 3 ^ 40 * 4875043 * 2
def baseEnd_4875043 : Nat := 834413423445558368514197

theorem tailTrace_4875043 : CollatzResearch.WordTrace tailWord_4875043 prefixEnd_4875043 834413423445558368514197 := by
  unfold tailWord_4875043
  simp only [CollatzResearch.WordTrace]
  refine ⟨177807425677559276903549783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118538283785039517935699855 177807425677559276903549783)
  ·
    refine ⟨266711138516338915355324675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177807425677559276903549783 266711138516338915355324675)
    ·
      refine ⟨400066707774508373032987013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266711138516338915355324675 400066707774508373032987013)
      ·
        refine ⟨75012507707720319943685065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 400066707774508373032987013 75012507707720319943685065)
        ·
          refine ⟨56259380780790239957763799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75012507707720319943685065 56259380780790239957763799)
          ·
            refine ⟨84389071171185359936645699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56259380780790239957763799 84389071171185359936645699)
            ·
              refine ⟨126583606756778039904968549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84389071171185359936645699 126583606756778039904968549)
              ·
                refine ⟨23734426266895882482181603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126583606756778039904968549 23734426266895882482181603)
                ·
                  refine ⟨35601639400343823723272405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23734426266895882482181603 35601639400343823723272405)
                  ·
                    refine ⟨834413423445558368514197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35601639400343823723272405 834413423445558368514197)
                    ·
                      rfl

theorem cell23_4875043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 7].length) (baseStart_4875043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875043 prefixEnd_4875043 := by exact prefixLift 4875043
  have htrace : WordTrace (prefixWord ++ tailWord_4875043) baseStart_4875043 baseEnd_4875043 := by
    simpa [prefixWord, tailWord_4875043, baseEnd_4875043] using wordTrace_append hprefix tailTrace_4875043
  have hstable : (prefixWord ++ tailWord_4875043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875043).length < 2 ^ (prefixWord ++ tailWord_4875043).sum := by decide
  have hdescent : baseEnd_4875043 < baseStart_4875043 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875080 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_4875080 : Nat := 118140960795 + 4875080 * 2 ^ 59
def prefixEnd_4875080 : Nat := 4983230072969 + 3 ^ 40 * 4875080 * 2
def baseEnd_4875080 : Nat := 2503259269120891460779921

theorem tailTrace_4875080 : CollatzResearch.WordTrace tailWord_4875080 prefixEnd_4875080 2503259269120891460779921 := by
  unfold tailWord_4875080
  simp only [CollatzResearch.WordTrace]
  refine ⟨88904387589212616111323347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118539183452283488148431129 88904387589212616111323347)
  ·
    refine ⟨133356581383818924166985021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88904387589212616111323347 133356581383818924166985021)
    ·
      refine ⟨50008718018932096562619383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133356581383818924166985021 50008718018932096562619383)
      ·
        refine ⟨75013077028398144843929075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50008718018932096562619383 75013077028398144843929075)
        ·
          refine ⟨112519615542597217265893613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75013077028398144843929075 112519615542597217265893613)
          ·
            refine ⟨42194855828473956474710105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112519615542597217265893613 42194855828473956474710105)
            ·
              refine ⟨31646141871355467356032579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42194855828473956474710105 31646141871355467356032579)
              ·
                refine ⟨47469212807033201034048869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31646141871355467356032579 47469212807033201034048869)
                ·
                  refine ⟨8900477401318725193884163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47469212807033201034048869 8900477401318725193884163)
                  ·
                    refine ⟨13350716101978087790826245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8900477401318725193884163 13350716101978087790826245)
                    ·
                      refine ⟨2503259269120891460779921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13350716101978087790826245 2503259269120891460779921)
                      ·
                        rfl

theorem cell23_4875080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_4875080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875080 prefixEnd_4875080 := by exact prefixLift 4875080
  have htrace : WordTrace (prefixWord ++ tailWord_4875080) baseStart_4875080 baseEnd_4875080 := by
    simpa [prefixWord, tailWord_4875080, baseEnd_4875080] using wordTrace_append hprefix tailTrace_4875080
  have hstable : (prefixWord ++ tailWord_4875080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875080).length < 2 ^ (prefixWord ++ tailWord_4875080).sum := by decide
  have hdescent : baseEnd_4875080 < baseStart_4875080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875097 : List Nat := [1, 2, 1, 2, 2, 4, 2, 1, 2, 4, 2]
def baseStart_4875097 : Nat := 118140960795 + 4875097 * 2 ^ 59
def prefixEnd_4875097 : Nat := 4983230072969 + 3 ^ 40 * 4875097 * 2
def baseEnd_4875097 : Nat := 2503267998292017894267343

theorem tailTrace_4875097 : CollatzResearch.WordTrace tailWord_4875097 prefixEnd_4875097 2503267998292017894267343 := by
  unfold tailWord_4875097
  simp only [CollatzResearch.WordTrace]
  refine ⟨177809395219363644126015545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118539596812909096084010363 177809395219363644126015545)
  ·
    refine ⟨133357046414522733094511659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177809395219363644126015545 133357046414522733094511659)
    ·
      refine ⟨200035569621784099641767489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133357046414522733094511659 200035569621784099641767489)
      ·
        refine ⟨150026677216338074731325617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200035569621784099641767489 150026677216338074731325617)
        ·
          refine ⟨112520007912253556048494213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150026677216338074731325617 112520007912253556048494213)
          ·
            refine ⟨21097501483547541759092665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112520007912253556048494213 21097501483547541759092665)
            ·
              refine ⟨15823126112660656319319499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21097501483547541759092665 15823126112660656319319499)
              ·
                refine ⟨23734689168990984478979249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15823126112660656319319499 23734689168990984478979249)
                ·
                  refine ⟨17801016876743238359234437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23734689168990984478979249 17801016876743238359234437)
                  ·
                    refine ⟨3337690664389357192356457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17801016876743238359234437 3337690664389357192356457)
                    ·
                      refine ⟨2503267998292017894267343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337690664389357192356457 2503267998292017894267343)
                      ·
                        rfl

theorem cell23_4875097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 1, 2, 4, 2].length) (baseStart_4875097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875097 prefixEnd_4875097 := by exact prefixLift 4875097
  have htrace : WordTrace (prefixWord ++ tailWord_4875097) baseStart_4875097 baseEnd_4875097 := by
    simpa [prefixWord, tailWord_4875097, baseEnd_4875097] using wordTrace_append hprefix tailTrace_4875097
  have hstable : (prefixWord ++ tailWord_4875097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875097).length < 2 ^ (prefixWord ++ tailWord_4875097).sum := by decide
  have hdescent : baseEnd_4875097 < baseStart_4875097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875107 : List Nat := [1, 1, 1, 5, 3, 1, 2, 2, 3, 4]
def baseStart_4875107 : Nat := 118140960795 + 4875107 * 2 ^ 59
def prefixEnd_4875107 : Nat := 4983230072969 + 3 ^ 40 * 4875107 * 2
def baseEnd_4875107 : Nat := 834424377699520951714099

theorem tailTrace_4875107 : CollatzResearch.WordTrace tailWord_4875107 prefixEnd_4875107 834424377699520951714099 := by
  unfold tailWord_4875107
  simp only [CollatzResearch.WordTrace]
  refine ⟨177809759949327415833879575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118539839966218277222586383 177809759949327415833879575)
  ·
    refine ⟨266714639923991123750819363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177809759949327415833879575 266714639923991123750819363)
    ·
      refine ⟨400071959885986685626229045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266714639923991123750819363 400071959885986685626229045)
      ·
        refine ⟨37506746239311251777458973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 400071959885986685626229045 37506746239311251777458973)
        ·
          refine ⟨14065029839741719416547115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37506746239311251777458973 14065029839741719416547115)
          ·
            refine ⟨21097544759612579124820673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14065029839741719416547115 21097544759612579124820673)
            ·
              refine ⟨15823158569709434343615505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21097544759612579124820673 15823158569709434343615505)
              ·
                refine ⟨11867368927282075757711629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15823158569709434343615505 11867368927282075757711629)
                ·
                  refine ⟨4450263347730778409141861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11867368927282075757711629 4450263347730778409141861)
                  ·
                    refine ⟨834424377699520951714099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450263347730778409141861 834424377699520951714099)
                    ·
                      rfl

theorem cell23_4875107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 3, 4].length) (baseStart_4875107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875107 prefixEnd_4875107 := by exact prefixLift 4875107
  have htrace : WordTrace (prefixWord ++ tailWord_4875107) baseStart_4875107 baseEnd_4875107 := by
    simpa [prefixWord, tailWord_4875107, baseEnd_4875107] using wordTrace_append hprefix tailTrace_4875107
  have hstable : (prefixWord ++ tailWord_4875107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875107).length < 2 ^ (prefixWord ++ tailWord_4875107).sum := by decide
  have hdescent : baseEnd_4875107 < baseStart_4875107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
